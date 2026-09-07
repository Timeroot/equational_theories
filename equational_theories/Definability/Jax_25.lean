import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq39 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
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
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
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
  have eq57 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X1 X1 X2
       have j1 := eq49 X1 X1 X2
       grind)
    | (have r₁ := eq39 X0 X1 X2
       have r₂ := eq49 X0 X1 X2
       grind)
    | (have r₁ := eq39 X1 X0 X2
       have r₂ := eq49 X0 X1 X2
       grind)
    | (have r₁ := eq39 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq49 X0 X1 X2
       grind)
    | exact resolve eq39 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq49
  have eq141 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq142 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq143 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq232 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq143 (σ X0) (σ X1)
       grind)
    | exact superpose eq143 eq15
    | (have j1 := eq143 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq143 (τ X0) X1
       grind)
    | exact superpose eq143 eq18
    | (have j1 := eq143 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq143
  have eq638 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq234 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq234
    | exact resolve eq234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq669 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq638 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq638
    | (have j0 := eq638 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq2005 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq232 x y
       grind)
    | exact superpose eq232 eq16
    | (have j1 := eq232 x y
       grind)
    | exact resolve eq16 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq2110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2005
       have i₂ := eq669 x y
       grind)
    | exact superpose eq669 eq2005
    | (have j1 := eq669 (σ x) (σ y)
       grind)
    | (have r₁ := eq2005
       have r₂ := eq669 x y
       grind)
    | (have r₁ := eq2005
       have r₂ := eq669 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2005
       have r₂ := eq669 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2005 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq2005
  have eq2111 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2110
  have eq2200 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2111
       grind)
    | exact superpose eq2111 eq10
    | exact resolve eq10 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2243 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2200
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2200
    | exact resolve eq2200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2244 : x = y := by grind
  clear eq2243
  have eq2356 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2244
       grind)
    | exact superpose eq2244 eq16
    | exact resolve eq16 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq2357 : False := by grind
  exact eq2357

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pyx_Equation4461 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4461 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X2) X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 x X1 X3
       have i₂ := eq9 x X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X1)
       have i₂ := eq9 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X1) X2
       have i₂ := eq9 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 X1) X2
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq70 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq78 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq70 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq84 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq86 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op X0 X2) ∨ (M.op X3 X3) = X3 ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X1 X2 X0
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X3 X3
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X1)
       have i₂ := eq25 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq9 X2 X3 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op X0 X2) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq113 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq113 X0 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq113 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq162 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 X3 (M.op X1 X3)
       have i₂ := eq9 X3 X1 X0
       grind)
    | exact superpose eq9 eq28
    | exact resolve eq28 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 (M.op X3 X3) X1
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq28
    | exact resolve eq28 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq202 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq206 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
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
  have eq208 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq202 (τ X0)
       grind)
    | exact superpose eq202 eq39
    | exact resolve eq39 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq208 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq208
    | exact resolve eq208 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq217 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq206 X0
       have i₂ := eq202 X0
       grind)
    | exact superpose eq202 eq206
    | exact resolve eq206 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq234 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = (M.op (M.op X3 X2) (M.op (M.op X4 X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X4 X3 X2 (M.op X1 X1)
       have i₂ := eq9 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X2) X0)) = (M.op (M.op X4 X1) (M.op (M.op X5 X5) X4)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq23 X5 X4 X1 x
       have i₂ := eq23 X2 X0 X1 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X1 (M.op X4 X4)) X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X4 (M.op X1 (M.op X4 X4)) X3 X2
       have i₂ := eq28 (M.op X4 X4) X1 X0
       grind)
    | (have i₁ := eq23 X4 (M.op X1 (M.op X4 X4)) X3 X2
       have i₂ := eq28 X0 X1 (M.op X4 X4)
       grind)
    | exact superpose eq28 eq23
    | exact resolve eq23 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op (M.op X3 X3) X0)) = (M.op (M.op X4 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X1 X2 X2 X4
       have i₂ := eq23 X3 X0 (M.op (M.op X1 X1) X2) X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (M.op X3 X3) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X3) X1) X1
       have i₂ := eq23 X3 X1 X1 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (M.op (M.op X1 X1) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq23 X1 (M.op X1 X1) (M.op X1 X1) X0
       grind)
    | exact superpose eq23 eq13
    | (have j0 := eq13 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x x) (M.op x x))
       have r₂ := eq23 x (M.op x x) (M.op x x) x
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X1 X2 : G, (M.op X2 X2) = X2 ∨ (k X2 (M.op (M.op X1 X1) (M.op X1 X1))) = X2 := by
    intro X1 X2
    first
    | (have j0 := eq303 x X1 X2
       grind)
    | (have r₁ := eq303 x x X2
       have r₂ := eq25 x (M.op x x) x
       grind)
    | (have r₁ := eq303 x x X2
       have r₂ := eq25 x (M.op x x) x
       grind)
    | exact resolve eq303 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq329 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 X3) X2)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 X2 X1 (σ X0)
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq23
    | exact resolve eq23 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (σ X0)
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq25
    | exact resolve eq25 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq334 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq329 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq329 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq356 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X4 (M.op X5 (M.op X4 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq24 X5 X4 x x
       have i₂ := eq24 X1 X0 x x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X4 X4) X3) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 x (M.op X4 X4) X3 X2
       have i₂ := eq24 X1 X0 X4 x
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op (M.op X4 (M.op X3 X3)) (M.op (M.op X5 X5) X4)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq23 X5 X4 (M.op X3 X3) x
       have i₂ := eq24 X1 X0 X3 x
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq403 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X3 X3) X4)) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq28 (M.op X2 X2) (M.op X3 X3) X4
       have i₂ := eq24 X1 X0 X2 X3
       grind)
    | exact superpose eq24 eq28
    | exact resolve eq28 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) (M.op X3 X3)) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op X3 X3) X4
       have i₂ := eq24 X1 X0 X2 X3
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X3 (M.op x x)
       have i₂ := eq24 X1 X0 x x
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X3 X4)) = (M.op (M.op X2 (M.op X3 X2)) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq28 (M.op X2 (M.op X3 X2)) X3 X4
       have i₂ := eq24 X2 X3 X1 X0
       grind)
    | exact superpose eq24 eq28
    | exact resolve eq28 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op X1 (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) (τ X0) X1
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq28
    | exact resolve eq28 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (M.op X1 X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq9
    | exact resolve eq9 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (τ X0)
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq9
    | exact resolve eq9 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (τ X0)
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq25
    | exact resolve eq25 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq454 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) = (M.op (M.op X3 (M.op (M.op X4 X4) X3)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq27 X3 X4 (M.op X1 X2) X2
       have i₂ := eq28 X2 X1 X0
       grind)
    | (have i₁ := eq27 X3 X4 (M.op X1 X2) X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq27
    | exact resolve eq27 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq833 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (σ (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq333 X2 (τ X0) X1
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq333
    | exact resolve eq333 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq1140 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ (M.op X1 X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X1 (τ X0) (τ X0)
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq438
    | exact resolve eq438 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1177 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (τ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq438 (τ X0) X1 X2
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq438
    | exact resolve eq438 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1909 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X2) = X0 ∨ (M.op X2 X3) = (k X3 X2) := by
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
  have eq1952 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0
       have i₂ := eq85 X0 X0 X1
       grind)
    | exact superpose eq85 eq202
    | (have j1 := eq85 X0 X0 X1
       grind)
    | exact resolve eq202 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq202
  have eq1973 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1952 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq1975 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X2) = X0 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1909 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909
  have eq2069 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1973 X0 (τ X1)
       grind)
    | exact superpose eq1973 eq17
    | (have j1 := eq1973 X0 X1
       grind)
    | exact resolve eq17 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2679 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X1) = (M.op (τ (τ (M.op X0 X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq833 (τ X0) X1 X2
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq833
    | exact resolve eq833 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq3534 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X2 (M.op (M.op (M.op X0 X0) X1) X2)) ∨ (M.op X3 (M.op (M.op X0 X0) X1)) = (k (M.op (M.op X0 X0) X1) X3) ∨ (M.op X1 X4) = (k X4 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq38 X0 X0 X2
       have i₂ := eq86 X0 X1 X2
       grind)
    | (have i₁ := eq38 X0 (M.op X1 X1) X2
       have i₂ := eq86 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq86 eq38
    | (have j1 := eq86 X3 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq38 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq86
  have eq3635 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X0 X0) X1)) = (k (M.op (M.op X0 X0) X1) X3) ∨ (M.op X1 X4) = (k X4 X1) := by
    intro X0 X1 X3 X4
    first
    | (have j0 := eq3534 X0 X1 x X3 X4
       grind)
    | (have r₁ := eq3534 X3 X1 x X3 X4
       have r₂ := eq297 X3 X1 x X3
       grind)
    | exact resolve eq3534 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq3534
  have eq4257 : ∀ X0 X1 X3 : G, (M.op (τ (τ (M.op X0 X0))) X1) = (M.op (τ (τ (M.op X3 X3))) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1177 X3 x X1
       have i₂ := eq1177 X0 x X1
       grind)
    | exact superpose eq1177 eq1177
    | exact resolve eq1177 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4317 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (τ (τ (M.op X0 X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1177 (τ X0) X1 X2
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq1177
    | exact resolve eq1177 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq12700 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (τ (τ (τ (M.op X0 X0))))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4317 (τ X0) X1 X2
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq4317
    | exact resolve eq4317 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14841 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op (M.op (M.op X3 X3) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X3) X1) X1
       have i₂ := eq162 X3 X1 X0 X1
       grind)
    | exact superpose eq162 eq9
    | exact resolve eq9 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq23402 : ∀ X0 X1 X2 X3 : G, (M.op (τ X2) (τ (M.op X2 X2))) = (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op (τ X2) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq436 X2 (M.op X3 X3)
       have i₂ := eq413 X0 X1 X3 (M.op (τ X2) (M.op X3 X3))
       grind)
    | exact superpose eq413 eq436
    | exact resolve eq436 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq436
  have eq25809 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq308 X1 X2
       have i₂ := eq9 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq9 eq308
    | (have j0 := eq308 X1 X2
       grind)
    | exact resolve eq308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq38454 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2069 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2069
    | (have j0 := eq2069 X1 X1
       grind)
    | exact resolve eq2069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq39026 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38454 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq38454
    | (have j0 := eq38454 X0 X1
       grind)
    | exact resolve eq38454 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38454
  have eq100811 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq334 X0 X1
       grind)
    | exact superpose eq334 eq10
    | (have j1 := eq334 X0 X1
       grind)
    | exact resolve eq10 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq100888 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq100811 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100811
    | (have j0 := eq100811 X0 X1
       grind)
    | exact resolve eq100811 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100811
  have eq103440 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq100888 X0 (σ X1)
       grind)
    | exact superpose eq100888 eq15
    | (have j1 := eq100888 X0 X1
       grind)
    | exact resolve eq15 eq100888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100888
  have eq111551 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103440 x y
       grind)
    | exact superpose eq103440 eq16
    | (have j1 := eq103440 x x
       grind)
    | exact resolve eq16 eq103440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103440
  have eq112675 : x = (M.op x x) := by
    first
    | (have j1 := eq39026 x x
       grind)
    | (have r₁ := eq111551
       have r₂ := eq39026 y x
       grind)
    | exact resolve eq111551 eq39026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39026 eq111551
  have eq115268 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq112675
       grind)
    | exact resolve eq12 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115269 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq112675
       grind)
    | exact resolve eq13 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115272 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X2))) = (M.op x (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 X1 X0 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq24
    | exact resolve eq24 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq115292 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135 x X2 X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq135
    | exact resolve eq135 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115293 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X2) x) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135 X2 x X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq135
    | exact resolve eq135 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq115306 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = (M.op (M.op X3 X2) (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq234 X0 X1 X2 X3 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq234
    | exact resolve eq234 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq115308 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X2) X0)) = (M.op (M.op X3 X1) (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq235 X0 X1 X2 X3 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq235
    | exact resolve eq235 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq115325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op x X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq273 X0 X1 X2 x X3
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq273
    | exact resolve eq273 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq115353 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X1) = (M.op (M.op X0 X1) (M.op x X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq331 X2 X1 X0 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq331
    | exact resolve eq331 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq115380 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X1) (M.op X2 (M.op X3 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq393 X2 X3 X0 X1 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq393
    | exact resolve eq393 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq115383 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (τ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq438 x X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq438
    | exact resolve eq438 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq115384 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (τ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq448 x X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq448
    | exact resolve eq448 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq115393 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1140 X0 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq1140
    | exact resolve eq1140 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq115403 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (τ (τ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2679 x X1 X0
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq2679
    | exact resolve eq2679 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115407 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) X1) = (M.op (τ (τ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4257 X0 X1 x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq4257
    | exact resolve eq4257 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257
  have eq115429 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq28
    | exact resolve eq28 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq115435 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op x (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 x x X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq167
    | exact resolve eq167 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq115449 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x (M.op X2 X2)) X1) (M.op x x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq268 x x X0 X1 X2
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq268
    | exact resolve eq268 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq115459 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op x (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X0 X1 x x
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq356
    | exact resolve eq356 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq115471 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq115269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115269
  have eq115472 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq115268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115268
  have eq115482 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq115459 X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115459
    | exact resolve eq115459 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115459
  have eq115486 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x (M.op X2 X2)) X1) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115449 X0 X1 X2
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115449
    | exact resolve eq115449 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115449
  have eq115490 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq115435 X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115435
    | exact resolve eq115435 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115435
  have eq115493 : ∀ X0 : G, x = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq115429 X0
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115429
    | exact resolve eq115429 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115429
  have eq115495 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X1) (M.op X2 (M.op (τ x) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115380 X0 X1 X2 x
       have i₂ := eq115383 x X2
       grind)
    | exact superpose eq115383 eq115380
    | exact resolve eq115380 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115380
  have eq115521 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x X0)) = (M.op (τ (τ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq115353 X0 X1 x
       have i₂ := eq115403 x X1
       grind)
    | exact superpose eq115403 eq115353
    | exact resolve eq115353 eq115403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115353 eq115403
  have eq115545 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X0 (M.op (τ x) X2)) (M.op x X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq115325 X0 x X2 X3
       have i₂ := eq115384 x X2
       grind)
    | exact superpose eq115384 eq115325
    | exact resolve eq115325 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115325
  have eq115562 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) (M.op x X3)) = (M.op (M.op X0 X1) (M.op (τ x) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq115308 X0 X1 x X3
       have i₂ := eq115384 x X0
       grind)
    | exact superpose eq115384 eq115308
    | exact resolve eq115308 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115308
  have eq115564 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op x X3)) = (M.op (M.op (τ x) (M.op X1 X1)) X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq115306 x X1 X2 X3
       have i₂ := eq115383 x (M.op X1 X1)
       grind)
    | exact superpose eq115383 eq115306
    | exact resolve eq115306 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115306
  have eq115576 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (τ x) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq115293 X0 X1 x
       have i₂ := eq115384 x x
       grind)
    | exact superpose eq115384 eq115293
    | exact resolve eq115293 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115293
  have eq115577 : ∀ X1 X2 : G, (M.op (M.op x (M.op X2 X2)) X1) = (M.op (τ x) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq115292 x X1 X2
       have i₂ := eq115383 x X1
       grind)
    | exact superpose eq115383 eq115292
    | exact resolve eq115292 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115292
  have eq115592 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op X1 (M.op (τ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115272 X0 X1 x
       have i₂ := eq115383 x X1
       grind)
    | exact superpose eq115383 eq115272
    | exact resolve eq115272 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115272
  have eq115598 : ∀ X0 X1 : G, x = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115482 X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115482
    | exact resolve eq115482 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115482
  have eq115600 : ∀ X1 X2 : G, (M.op (τ x) X1) = (M.op (M.op (M.op x (M.op X2 X2)) X1) x) := by
    intro X1 X2
    first
    | (have i₁ := eq115486 x X1 X2
       have i₂ := eq115384 x X1
       grind)
    | exact superpose eq115384 eq115486
    | exact resolve eq115486 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115486
  have eq115604 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115490 X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115490
    | exact resolve eq115490 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115490
  have eq115606 : x = (M.op (τ x) x) := by
    first
    | (have i₁ := eq115493 x
       have i₂ := eq115383 x x
       grind)
    | exact superpose eq115383 eq115493
    | exact resolve eq115493 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115493
  have eq115608 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X1) (M.op (τ x) (τ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq115495 X0 X1 x
       have i₂ := eq115383 x (τ x)
       grind)
    | exact superpose eq115383 eq115495
    | exact resolve eq115495 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115495
  have eq115647 : ∀ X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (τ (τ x)) (M.op (τ x) X2)) := by
    intro X2 X3
    first
    | (have i₁ := eq115545 x X2 X3
       have i₂ := eq115521 x (M.op (τ x) X2)
       grind)
    | exact superpose eq115521 eq115545
    | exact resolve eq115545 eq115521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115545
  have eq115662 : ∀ X0 X1 : G, (M.op (τ (τ x)) X1) = (M.op (M.op X0 X1) (M.op (τ x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115562 X0 X1 x
       have i₂ := eq115521 x X1
       grind)
    | exact superpose eq115521 eq115562
    | exact resolve eq115562 eq115521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115562
  have eq115664 : ∀ X1 X2 : G, (M.op (M.op (τ x) (M.op X1 X1)) X2) = (M.op (τ (τ x)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq115564 X1 X2 x
       have i₂ := eq115521 x X2
       grind)
    | exact superpose eq115521 eq115564
    | exact resolve eq115564 eq115521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115521 eq115564
  have eq115673 : ∀ X1 : G, (M.op (τ x) X1) = (M.op (M.op (τ x) x) X1) := by
    intro X1
    first
    | (have i₁ := eq115576 x X1
       have i₂ := eq115383 x X1
       grind)
    | exact superpose eq115383 eq115576
    | exact resolve eq115576 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115576
  have eq115681 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op (τ x) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq115592 X0 x
       have i₂ := eq115383 x (τ x)
       grind)
    | exact superpose eq115383 eq115592
    | exact resolve eq115592 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115592
  have eq115684 : ∀ X0 : G, x = (M.op X0 (M.op (τ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq115598 X0 x
       have i₂ := eq115383 x X0
       grind)
    | exact superpose eq115383 eq115598
    | exact resolve eq115598 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115598
  have eq115686 : ∀ X1 : G, (M.op (τ x) X1) = (M.op (M.op (τ x) X1) x) := by
    intro X1
    first
    | (have i₁ := eq115600 X1 x
       have i₂ := eq115577 X1 x
       grind)
    | exact superpose eq115577 eq115600
    | exact resolve eq115600 eq115577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115577 eq115600
  have eq115689 : ∀ X1 : G, x = (M.op (τ x) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq115604 x X1
       have i₂ := eq115383 x (M.op X1 X1)
       grind)
    | exact superpose eq115383 eq115604
    | exact resolve eq115604 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115604
  have eq115690 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X1) (τ (M.op x x))) := by
    intro X0 X1
    first
    | (have i₁ := eq115608 X0 X1
       have i₂ := eq215 x
       grind)
    | exact superpose eq215 eq115608
    | exact resolve eq115608 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115608
  have eq115712 : ∀ X2 : G, (M.op (τ x) X2) = (M.op (τ (τ x)) (M.op (τ x) X2)) := by
    intro X2
    first
    | (have i₁ := eq115647 X2 x
       have i₂ := eq115384 x X2
       grind)
    | exact superpose eq115384 eq115647
    | exact resolve eq115647 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115647
  have eq115725 : ∀ X1 : G, (M.op x X1) = (M.op (τ x) X1) := by
    intro X1
    first
    | (have i₁ := eq115673 X1
       have i₂ := eq115606
       grind)
    | exact superpose eq115606 eq115673
    | exact resolve eq115673 eq115606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115673
  have eq115731 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (τ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq115681 X0
       have i₂ := eq215 x
       grind)
    | exact superpose eq215 eq115681
    | exact resolve eq115681 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115681
  have eq115734 : x = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq115684 x
       have i₂ := eq115383 x (τ x)
       grind)
    | exact superpose eq115383 eq115684
    | exact resolve eq115684 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115684
  have eq115738 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X1) (τ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq115690 X0 X1
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115690
    | exact resolve eq115690 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115690
  have eq115757 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq115731 X0
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115731
    | exact resolve eq115731 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115731
  have eq115759 : x = (τ (M.op x x)) := by
    first
    | (have i₁ := eq115734
       have i₂ := eq215 x
       grind)
    | exact superpose eq215 eq115734
    | exact resolve eq115734 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115734
  have eq115762 : ∀ X1 : G, (M.op (τ x) X1) = (M.op (M.op x X1) (τ x)) := by
    intro X1
    first
    | (have i₁ := eq115738 x X1
       have i₂ := eq115384 x X1
       grind)
    | exact superpose eq115384 eq115738
    | exact resolve eq115738 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115738
  have eq115780 : x = (τ x) := by
    first
    | (have i₁ := eq115759
       have i₂ := eq112675
       grind)
    | exact superpose eq112675 eq115759
    | exact resolve eq115759 eq112675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112675 eq115759
  have eq115783 : ∀ X1 : G, (M.op x X1) = (M.op (M.op x X1) (τ x)) := by
    intro X1
    first
    | (have i₁ := eq115762 X1
       have i₂ := eq115725 X1
       grind)
    | exact superpose eq115725 eq115762
    | exact resolve eq115762 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115762
  have eq115799 : ∀ X1 : G, (M.op x X1) = (M.op (M.op x X1) x) := by
    intro X1
    first
    | (have i₁ := eq115783 X1
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq115783
    | exact resolve eq115783 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115783
  have eq117251 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4317 X5 (M.op X3 (M.op X4 X3)) X4
       have i₂ := eq394 X4 X3 X1 X0 X2
       grind)
    | exact superpose eq394 eq4317
    | exact resolve eq4317 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117254 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq12700 X5 (M.op X3 (M.op X4 X3)) X4
       have i₂ := eq394 X4 X3 X1 X0 X2
       grind)
    | exact superpose eq394 eq12700
    | exact resolve eq12700 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117259 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op (M.op X3 (M.op X4 X3)) (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq14841 (M.op X3 (M.op X4 X3)) X4 X5 X6
       have i₂ := eq394 X4 X3 X1 X0 X2
       grind)
    | exact superpose eq394 eq14841
    | exact resolve eq14841 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14841
  have eq117389 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0)) = (M.op (τ (τ (M.op X5 X5))) (M.op X4 (M.op (σ (M.op X3 X3)) X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2679 X5 (M.op X4 (M.op (σ (M.op X3 X3)) X4)) X3
       have i₂ := eq394 (σ (M.op X3 X3)) X4 X1 X0 X2
       grind)
    | exact superpose eq394 eq2679
    | exact resolve eq2679 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq2679
  have eq118026 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0)) = (M.op (τ (τ x)) (M.op X4 (M.op (σ (M.op X3 X3)) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq117389 X0 X1 X2 X3 X4 x
       have i₂ := eq115407 x (M.op X4 (M.op (σ (M.op X3 X3)) X4))
       grind)
    | exact superpose eq115407 eq117389
    | exact resolve eq117389 eq115407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115407 eq117389
  have eq118127 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op (M.op X3 (M.op X4 X3)) (M.op (M.op X0 (M.op X1 X1)) (M.op (τ x) X0))) := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq117259 X0 X1 x X3 X4 X5 X6
       have i₂ := eq115384 x X0
       grind)
    | exact superpose eq115384 eq117259
    | exact resolve eq117259 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117259
  have eq118129 : ∀ X0 X1 X3 X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (M.op X0 (M.op X1 X1)) (M.op (τ x) X0))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq117254 X0 X1 x X3 X4 X5
       have i₂ := eq115384 x X0
       grind)
    | exact superpose eq115384 eq117254
    | exact resolve eq117254 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117254
  have eq118131 : ∀ X0 X1 X3 X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (M.op X0 (M.op X1 X1)) (M.op (τ x) X0))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq117251 X0 X1 x X3 X4 X5
       have i₂ := eq115384 x X0
       grind)
    | exact superpose eq115384 eq117251
    | exact resolve eq117251 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117251
  have eq119043 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0)) = (M.op (τ (τ x)) (M.op (τ x) (σ (M.op X3 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118026 X0 X1 X2 X3 x
       have i₂ := eq115383 x (σ (M.op X3 X3))
       grind)
    | exact superpose eq115383 eq118026
    | exact resolve eq118026 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118026
  have eq119144 : ∀ X1 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op (M.op X3 (M.op X4 X3)) (M.op (τ (τ x)) (M.op X1 X1))) := by
    intro X1 X3 X4 X5 X6
    first
    | (have i₁ := eq118127 x X1 X3 X4 X5 X6
       have i₂ := eq115662 x (M.op X1 X1)
       grind)
    | exact superpose eq115662 eq118127
    | exact resolve eq118127 eq115662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118127
  have eq119146 : ∀ X1 X3 X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (τ (τ x)) (M.op X1 X1))) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq118129 x X1 X3 X4 X5
       have i₂ := eq115662 x (M.op X1 X1)
       grind)
    | exact superpose eq115662 eq118129
    | exact resolve eq118129 eq115662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118129
  have eq119148 : ∀ X1 X3 X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (τ (τ x)) (M.op X1 X1))) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq118131 x X1 X3 X4 X5
       have i₂ := eq115662 x (M.op X1 X1)
       grind)
    | exact superpose eq115662 eq118131
    | exact resolve eq118131 eq115662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118131
  have eq120055 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0)) = (M.op (τ x) (σ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119043 X0 X1 X2 X3
       have i₂ := eq115712 (σ (M.op X3 X3))
       grind)
    | exact superpose eq115712 eq119043
    | exact resolve eq119043 eq115712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115712 eq119043
  have eq120156 : ∀ X1 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op (M.op X3 (M.op X4 X3)) (M.op (τ x) (M.op X1 X1))) := by
    intro X1 X3 X4 X5 X6
    first
    | (have i₁ := eq119144 X1 X3 X4 X5 X6
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq119144
    | exact resolve eq119144 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119144
  have eq120158 : ∀ X1 X3 X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (τ x) (M.op X1 X1))) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq119146 X1 X3 X4 X5
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq119146
    | exact resolve eq119146 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119146
  have eq120160 : ∀ X1 X3 X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op (M.op X3 (M.op X4 X3)) (M.op (τ x) (M.op X1 X1))) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq119148 X1 X3 X4 X5
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq119148
    | exact resolve eq119148 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119148
  have eq121060 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X2) X0)) = (M.op x (σ (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq120055 X0 X1 X2 X3
       have i₂ := eq115725 (σ (M.op X3 X3))
       grind)
    | exact superpose eq115725 eq120055
    | exact resolve eq120055 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120055
  have eq121161 : ∀ X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op (M.op X3 (M.op X4 X3)) x) := by
    intro X3 X4 X5 X6
    first
    | (have i₁ := eq120156 x X3 X4 X5 X6
       have i₂ := eq115689 x
       grind)
    | exact superpose eq115689 eq120156
    | exact resolve eq120156 eq115689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120156
  have eq121163 : ∀ X3 X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op (M.op X3 (M.op X4 X3)) x) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq120158 x X3 X4 X5
       have i₂ := eq115689 x
       grind)
    | exact superpose eq115689 eq120158
    | exact resolve eq120158 eq115689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120158
  have eq121165 : ∀ X3 X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op (M.op X3 (M.op X4 X3)) x) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq120160 x X3 X4 X5
       have i₂ := eq115689 x
       grind)
    | exact superpose eq115689 eq120160
    | exact resolve eq120160 eq115689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120160
  have eq122062 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (τ x) X0)) = (M.op x (σ (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq121060 X0 X1 x X3
       have i₂ := eq115384 x X0
       grind)
    | exact superpose eq115384 eq121060
    | exact resolve eq121060 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121060
  have eq122163 : ∀ X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op (M.op (τ x) X4) x) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq121161 x X4 X5 X6
       have i₂ := eq115383 x X4
       grind)
    | exact superpose eq115383 eq121161
    | exact resolve eq121161 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121161
  have eq122165 : ∀ X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op (M.op (τ x) X4) x) := by
    intro X4 X5
    first
    | (have i₁ := eq121163 x X4 X5
       have i₂ := eq115383 x X4
       grind)
    | exact superpose eq115383 eq121163
    | exact resolve eq121163 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121163
  have eq122167 : ∀ X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op (M.op (τ x) X4) x) := by
    intro X4 X5
    first
    | (have i₁ := eq121165 x X4 X5
       have i₂ := eq115383 x X4
       grind)
    | exact superpose eq115383 eq121165
    | exact resolve eq121165 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121165
  have eq123036 : ∀ X1 X3 : G, (M.op (τ (τ x)) (M.op X1 X1)) = (M.op x (σ (M.op X3 X3))) := by
    intro X1 X3
    first
    | (have i₁ := eq122062 x X1 X3
       have i₂ := eq115662 x (M.op X1 X1)
       grind)
    | exact superpose eq115662 eq122062
    | exact resolve eq122062 eq115662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115662 eq122062
  have eq123137 : ∀ X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op (τ x) X4) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq122163 X4 X5 X6
       have i₂ := eq115686 X4
       grind)
    | exact superpose eq115686 eq122163
    | exact resolve eq122163 eq115686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122163
  have eq123139 : ∀ X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op (τ x) X4) := by
    intro X4 X5
    first
    | (have i₁ := eq122165 X4 X5
       have i₂ := eq115686 X4
       grind)
    | exact superpose eq115686 eq122165
    | exact resolve eq122165 eq115686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122165
  have eq123141 : ∀ X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op (τ x) X4) := by
    intro X4 X5
    first
    | (have i₁ := eq122167 X4 X5
       have i₂ := eq115686 X4
       grind)
    | exact superpose eq115686 eq122167
    | exact resolve eq122167 eq115686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122167
  have eq123976 : ∀ X1 X3 : G, (M.op (τ x) (M.op X1 X1)) = (M.op x (σ (M.op X3 X3))) := by
    intro X1 X3
    first
    | (have i₁ := eq123036 X1 X3
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq123036
    | exact resolve eq123036 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123036
  have eq124071 : ∀ X4 X5 X6 : G, (M.op X5 (M.op (M.op (M.op X6 X6) X4) X5)) = (M.op x X4) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq123137 X4 X5 X6
       have i₂ := eq115725 X4
       grind)
    | exact superpose eq115725 eq123137
    | exact resolve eq123137 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123137
  have eq124073 : ∀ X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) X4) = (M.op x X4) := by
    intro X4 X5
    first
    | (have i₁ := eq123139 X4 X5
       have i₂ := eq115725 X4
       grind)
    | exact superpose eq115725 eq123139
    | exact resolve eq123139 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123139
  have eq124075 : ∀ X4 X5 : G, (M.op (τ (τ (τ (M.op X5 X5)))) X4) = (M.op x X4) := by
    intro X4 X5
    first
    | (have i₁ := eq123141 X4 X5
       have i₂ := eq115725 X4
       grind)
    | exact superpose eq115725 eq123141
    | exact resolve eq123141 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123141
  have eq124851 : ∀ X3 : G, x = (M.op x (σ (M.op X3 X3))) := by
    intro X3
    first
    | (have i₁ := eq123976 x X3
       have i₂ := eq115689 x
       grind)
    | exact superpose eq115689 eq123976
    | exact resolve eq123976 eq115689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123976
  have eq124939 : ∀ X4 X6 : G, (M.op (τ x) (M.op (M.op X6 X6) X4)) = (M.op x X4) := by
    intro X4 X6
    first
    | (have i₁ := eq124071 X4 x X6
       have i₂ := eq115383 x (M.op (M.op X6 X6) X4)
       grind)
    | exact superpose eq115383 eq124071
    | exact resolve eq124071 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124071
  have eq125692 : ∀ X4 X6 : G, (M.op x (M.op (M.op X6 X6) X4)) = (M.op x X4) := by
    intro X4 X6
    first
    | (have i₁ := eq124939 X4 X6
       have i₂ := eq115725 (M.op (M.op X6 X6) X4)
       grind)
    | exact superpose eq115725 eq124939
    | exact resolve eq124939 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124939
  have eq126313 : ∀ X4 : G, (M.op x X4) = (M.op x (M.op (τ x) X4)) := by
    intro X4
    first
    | (have i₁ := eq125692 X4 x
       have i₂ := eq115384 x X4
       grind)
    | exact superpose eq115384 eq125692
    | exact resolve eq125692 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125692
  have eq126792 : ∀ X4 : G, (M.op x X4) = (M.op x (M.op x X4)) := by
    intro X4
    first
    | (have i₁ := eq126313 X4
       have i₂ := eq115725 X4
       grind)
    | exact superpose eq115725 eq126313
    | exact resolve eq126313 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126313
  have eq127631 : x = (σ x) := by
    first
    | (have i₁ := eq11 x
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq11
    | exact resolve eq11 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127635 : ∀ X0 : G, (τ (k x X0)) = (k x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 x
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq39
    | exact resolve eq39 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq127657 : ∀ X0 : G, (τ (k x X0)) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq127635 X0
       have i₂ := eq115472 (τ X0)
       grind)
    | exact superpose eq115472 eq127635
    | exact resolve eq127635 eq115472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127635
  have eq127663 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq127657 X0
       have i₂ := eq115472 X0
       grind)
    | exact superpose eq115472 eq127657
    | exact resolve eq127657 eq115472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115472 eq127657
  have eq129499 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) (M.op X4 X4)) = (M.op (M.op X2 (M.op X3 (M.op X2 X3))) (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq12700 X5 (M.op X2 (M.op X3 (M.op X2 X3))) (M.op X4 X4)
       have i₂ := eq403 X2 X3 X4 X1 X0
       grind)
    | exact superpose eq403 eq12700
    | exact resolve eq12700 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq12700
  have eq129512 : ∀ X1 X2 X3 X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) (M.op X4 X4)) = (M.op (M.op X2 (M.op X3 (M.op X2 X3))) (M.op (τ x) (M.op X1 X1))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq129499 x X1 X2 X3 X4 X5
       have i₂ := eq115383 x (M.op X1 X1)
       grind)
    | exact superpose eq115383 eq129499
    | exact resolve eq129499 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129499
  have eq130491 : ∀ X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) (M.op X4 X4)) = (M.op (τ x) (τ (M.op x x))) := by
    intro X4 X5
    first
    | (have i₁ := eq129512 x x x X4 X5
       have i₂ := eq23402 x x x x
       grind)
    | exact superpose eq23402 eq129512
    | exact resolve eq129512 eq23402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23402 eq129512
  have eq131470 : ∀ X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) (M.op X4 X4)) = (M.op (τ x) (τ x)) := by
    intro X4 X5
    first
    | (have i₁ := eq130491 X4 X5
       have i₂ := eq115393 x
       grind)
    | exact superpose eq115393 eq130491
    | exact resolve eq130491 eq115393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115393 eq130491
  have eq132339 : ∀ X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) (M.op X4 X4)) = (τ (M.op x x)) := by
    intro X4 X5
    first
    | (have i₁ := eq131470 X4 X5
       have i₂ := eq215 x
       grind)
    | exact superpose eq215 eq131470
    | exact resolve eq131470 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq131470
  have eq133205 : ∀ X4 X5 : G, (M.op (τ (τ (τ (τ (M.op X5 X5))))) (M.op X4 X4)) = (M.op (τ x) x) := by
    intro X4 X5
    first
    | (have i₁ := eq132339 X4 X5
       have i₂ := eq127663 x
       grind)
    | exact superpose eq127663 eq132339
    | exact resolve eq132339 eq127663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132339
  have eq134061 : ∀ X4 X5 : G, x = (M.op (τ (τ (τ (τ (M.op X5 X5))))) (M.op X4 X4)) := by
    intro X4 X5
    first
    | (have i₁ := eq133205 X4 X5
       have i₂ := eq115606
       grind)
    | exact superpose eq115606 eq133205
    | exact resolve eq133205 eq115606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133205
  have eq134895 : ∀ X4 : G, x = (M.op x (M.op X4 X4)) := by
    intro X4
    first
    | (have i₁ := eq134061 X4 x
       have i₂ := eq124073 (M.op X4 X4) x
       grind)
    | exact superpose eq124073 eq134061
    | exact resolve eq134061 eq124073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124073 eq134061
  have eq138633 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127631
       grind)
    | exact superpose eq127631 eq16
    | exact resolve eq16 eq127631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140453 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X1 X2)))) ∨ (M.op X3 X3) = (k (M.op X3 X3) (M.op X4 (M.op (M.op X5 X5) X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25809 X4 X5 (M.op X3 X3)
       have i₂ := eq404 X1 X2 X0 X3 X3
       grind)
    | exact superpose eq404 eq25809
    | (have j0 := eq25809 X4 X5 (M.op X3 X3)
       grind)
    | exact resolve eq25809 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq25809
  have eq140860 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (τ x) (M.op X1 (M.op X2 (M.op X1 X2)))) ∨ (M.op X3 X3) = (k (M.op X3 X3) (M.op X4 (M.op (M.op X5 X5) X4))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq140453 x X1 X2 X3 X4 X5
       have i₂ := eq115384 x (M.op X1 (M.op X2 (M.op X1 X2)))
       grind)
    | exact superpose eq115384 eq140453
    | (have j0 := eq140453 x X1 X2 X3 X4 X5
       grind)
    | exact resolve eq140453 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140453
  have eq141722 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op x (M.op X1 (M.op X2 (M.op X1 X2)))) ∨ (M.op X3 X3) = (k (M.op X3 X3) (M.op X4 (M.op (M.op X5 X5) X4))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq140860 X1 X2 X3 X4 X5
       have i₂ := eq115725 (M.op X1 (M.op X2 (M.op X1 X2)))
       grind)
    | exact superpose eq115725 eq140860
    | (have j0 := eq140860 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq140860 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140860
  have eq142582 : ∀ X1 X3 X4 X5 : G, (M.op X3 X3) = (M.op x (M.op X1 (M.op (τ x) X1))) ∨ (M.op X3 X3) = (k (M.op X3 X3) (M.op X4 (M.op (M.op X5 X5) X4))) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq141722 X1 x X3 X4 X5
       have i₂ := eq115383 x X1
       grind)
    | exact superpose eq115383 eq141722
    | (have j0 := eq141722 X1 x X3 X4 X5
       grind)
    | exact resolve eq141722 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141722
  have eq143337 : ∀ X3 X4 X5 : G, (M.op X3 X3) = (M.op x (M.op (τ x) (τ x))) ∨ (M.op X3 X3) = (k (M.op X3 X3) (M.op X4 (M.op (M.op X5 X5) X4))) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq142582 x X3 X4 X5
       have i₂ := eq115383 x (τ x)
       grind)
    | exact superpose eq115383 eq142582
    | (have j0 := eq142582 x X3 X4 X5
       grind)
    | exact resolve eq142582 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142582
  have eq144089 : ∀ X3 X4 X5 : G, (M.op X3 X3) = (τ x) ∨ (M.op X3 X3) = (k (M.op X3 X3) (M.op X4 (M.op (M.op X5 X5) X4))) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq143337 X3 X4 X5
       have i₂ := eq115757 (τ x)
       grind)
    | exact superpose eq115757 eq143337
    | (have j0 := eq143337 X3 X4 X5
       grind)
    | exact resolve eq143337 eq115757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115757 eq143337
  have eq144831 : ∀ X3 X4 X5 : G, x = (M.op X3 X3) ∨ (M.op X3 X3) = (k (M.op X3 X3) (M.op X4 (M.op (M.op X5 X5) X4))) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq144089 X3 X4 X5
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq144089
    | (have j0 := eq144089 X3 X4 X5
       grind)
    | exact resolve eq144089 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144089
  have eq145545 : ∀ X3 X5 : G, (M.op X3 X3) = (k (M.op X3 X3) (M.op (τ x) (M.op X5 X5))) ∨ x = (M.op X3 X3) := by
    intro X3 X5
    first
    | (have i₁ := eq144831 X3 x X5
       have i₂ := eq115383 x (M.op X5 X5)
       grind)
    | exact superpose eq115383 eq144831
    | (have j0 := eq144831 X3 x X5
       grind)
    | exact resolve eq144831 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144831
  have eq146229 : ∀ X3 : G, (M.op X3 X3) = (k (M.op X3 X3) x) ∨ x = (M.op X3 X3) := by
    intro X3
    first
    | (have i₁ := eq145545 X3 x
       have i₂ := eq115689 x
       grind)
    | exact superpose eq115689 eq145545
    | (have j0 := eq145545 X3 x
       grind)
    | exact resolve eq145545 eq115689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145545
  have eq173668 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) (M.op (τ (τ (τ (M.op X0 X0)))) X1)) = (M.op (M.op X3 (M.op X2 X3)) (M.op (M.op X4 X4) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq416 X4 X5 X3 X2 (M.op X1 X2)
       have i₂ := eq4317 X0 X2 X1
       grind)
    | exact superpose eq4317 eq416
    | exact resolve eq416 eq4317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq4317
  have eq177008 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X1 X2) (M.op (τ (τ (τ (M.op X0 X0)))) X1)) = (M.op (M.op X3 (M.op X2 X3)) (M.op (τ x) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq173668 X0 X1 X2 X3 x X5
       have i₂ := eq115384 x (M.op X5 X5)
       grind)
    | exact superpose eq115384 eq173668
    | exact resolve eq173668 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173668
  have eq178181 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (τ (τ (τ (M.op X0 X0)))) X1)) = (M.op (M.op X3 (M.op X2 X3)) x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177008 X0 X1 X2 X3 x
       have i₂ := eq115689 x
       grind)
    | exact superpose eq115689 eq177008
    | exact resolve eq177008 eq115689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177008
  have eq179343 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (τ (τ (τ (M.op X0 X0)))) X1)) = (M.op (M.op (τ x) X2) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178181 X0 X1 X2 x
       have i₂ := eq115383 x X2
       grind)
    | exact superpose eq115383 eq178181
    | exact resolve eq178181 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178181
  have eq180503 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (τ (τ (τ (M.op X0 X0)))) X1)) = (M.op (τ x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179343 X0 X1 X2
       have i₂ := eq115686 X2
       grind)
    | exact superpose eq115686 eq179343
    | exact resolve eq179343 eq115686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115686 eq179343
  have eq181618 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (τ (τ (τ (M.op X0 X0)))) X1)) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180503 X0 X1 X2
       have i₂ := eq115725 X2
       grind)
    | exact superpose eq115725 eq180503
    | exact resolve eq180503 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180503
  have eq182678 : ∀ X1 X2 : G, (M.op x X2) = (M.op (M.op X1 X2) (M.op x X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq181618 x X1 X2
       have i₂ := eq124075 X1 x
       grind)
    | exact superpose eq124075 eq181618
    | exact resolve eq181618 eq124075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124075 eq181618
  have eq208956 : ∀ X0 X1 : G, x = (M.op x (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124851 X0
       have i₂ := eq1973 X0 X1
       grind)
    | exact superpose eq1973 eq124851
    | (have j1 := eq1973 X0 X1
       grind)
    | exact resolve eq124851 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973 eq124851
  have eq211758 : ∀ X0 X1 X2 X3 : G, (M.op (τ (M.op X2 (M.op X2 X2))) (τ (M.op (M.op X0 (M.op (M.op X1 X1) X0)) (M.op X2 X2)))) = (M.op (M.op X3 X3) (τ (M.op X2 (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq437 (M.op X2 (M.op X2 X2)) X3
       have i₂ := eq454 X2 X2 (M.op X2 X2) X0 X1
       grind)
    | exact superpose eq454 eq437
    | exact resolve eq437 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq454
  have eq213001 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X2 (M.op X2 X2))) (τ (M.op (M.op X0 (M.op (M.op X1 X1) X0)) (M.op X2 X2)))) = (M.op (τ x) (τ (M.op X2 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq211758 X0 X1 X2 x
       have i₂ := eq115384 x (τ (M.op X2 (M.op X2 X2)))
       grind)
    | exact superpose eq115384 eq211758
    | exact resolve eq211758 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211758
  have eq214648 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X2 (M.op X2 X2))) (τ (M.op (M.op X0 (M.op (M.op X1 X1) X0)) (M.op X2 X2)))) = (M.op x (τ (M.op X2 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq213001 X0 X1 X2
       have i₂ := eq115725 (τ (M.op X2 (M.op X2 X2)))
       grind)
    | exact superpose eq115725 eq213001
    | exact resolve eq213001 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213001
  have eq216294 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (τ x) X2)) (τ (M.op (M.op X0 (M.op (M.op X1 X1) X0)) (M.op X2 X2)))) = (M.op x (τ (M.op (τ x) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214648 X0 X1 X1
       have i₂ := eq115383 X1 X1
       grind)
    | exact superpose eq115383 eq214648
    | exact resolve eq214648 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214648
  have eq217910 : ∀ X0 X1 X2 : G, (M.op (τ (M.op x X2)) (τ (M.op (M.op X0 (M.op (M.op X1 X1) X0)) (M.op X2 X2)))) = (M.op x (τ (M.op x X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216294 X0 X1 X1
       have i₂ := eq115725 X1
       grind)
    | exact superpose eq115725 eq216294
    | exact resolve eq216294 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216294
  have eq219368 : ∀ X1 X2 : G, (M.op x (τ (M.op x X2))) = (M.op (τ (M.op x X2)) (τ (M.op (M.op (τ x) (M.op X1 X1)) (M.op X2 X2)))) := by
    intro X1 X2
    first
    | (have i₁ := eq217910 x X1 X2
       have i₂ := eq115383 x (M.op X1 X1)
       grind)
    | exact superpose eq115383 eq217910
    | exact resolve eq217910 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217910
  have eq220814 : ∀ X2 : G, (M.op x (τ (M.op x X2))) = (M.op (τ (M.op x X2)) (τ (M.op (τ (τ x)) (M.op X2 X2)))) := by
    intro X2
    first
    | (have i₁ := eq219368 x X2
       have i₂ := eq115664 x (M.op X2 X2)
       grind)
    | exact superpose eq115664 eq219368
    | exact resolve eq219368 eq115664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115664 eq219368
  have eq222153 : ∀ X2 : G, (M.op x (τ (M.op x X2))) = (M.op (τ (M.op x X2)) (τ (M.op (τ x) (M.op X2 X2)))) := by
    intro X2
    first
    | (have i₁ := eq220814 X2
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq220814
    | exact resolve eq220814 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220814
  have eq223337 : ∀ X2 : G, (M.op x (τ (M.op x X2))) = (M.op (τ (M.op x X2)) (τ x)) := by
    intro X2
    first
    | (have i₁ := eq222153 X2
       have i₂ := eq115689 X2
       grind)
    | exact superpose eq115689 eq222153
    | exact resolve eq222153 eq115689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115689 eq222153
  have eq224317 : ∀ X2 : G, (M.op x (τ (M.op x X2))) = (M.op (τ (M.op x X2)) x) := by
    intro X2
    first
    | (have i₁ := eq223337 X2
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq223337
    | exact resolve eq223337 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223337
  have eq500186 : ∀ X0 : G, (τ (M.op x X0)) = (M.op (τ (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq127663 (M.op x X0)
       have i₂ := eq115799 X0
       grind)
    | exact superpose eq115799 eq127663
    | exact resolve eq127663 eq115799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115799 eq127663
  have eq750921 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1975 X0 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750923 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq750921 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750921
  have eq950372 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq750923 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750923
  have eq951772 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k X1 X2) = X1 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq950372 X1 X2
       have i₂ := eq143 X2 X0 X1 X3
       grind)
    | (have i₁ := eq950372 X2 (M.op X1 X1)
       have i₂ := eq143 X0 X1 X2 X3
       grind)
    | exact superpose eq143 eq950372
    | (have j0 := eq950372 X1 (M.op X0 X0)
       have j1 := eq143 X2 X1 X2 X3
       grind)
    | exact resolve eq950372 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq951907 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ (M.op X0 X0) = (k (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq950372 (M.op X0 X0) x
       have i₂ := eq134895 X0
       grind)
    | exact superpose eq134895 eq950372
    | (have j0 := eq950372 (M.op X0 X0) x
       grind)
    | exact resolve eq950372 eq134895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134895 eq950372
  have eq951960 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) x) := by
    intro X0
    first
    | (have j0 := eq951907 X0
       have j1 := eq146229 X0
       grind)
    | (have r₁ := eq951907 x
       have r₂ := eq146229 x
       grind)
    | exact resolve eq951907 eq146229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146229 eq951907
  have eq952086 : ∀ X1 X2 X3 : G, (M.op (τ x) X1) ≠ X1 ∨ (k X1 X2) = X1 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq951772 x X1 X2 X3
       have i₂ := eq115384 x X1
       grind)
    | exact superpose eq115384 eq951772
    | (have j0 := eq951772 x X1 X2 X3
       grind)
    | exact resolve eq951772 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951772
  have eq952197 : ∀ X1 X2 X3 : G, (M.op x X1) ≠ X1 ∨ (k X1 X2) = X1 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq952086 X1 X2 X3
       have i₂ := eq115725 X1
       grind)
    | exact superpose eq115725 eq952086
    | (have j0 := eq952086 X1 X2 X3
       grind)
    | exact resolve eq952086 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952086
  have eq953970 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) ≠ (M.op X1 (M.op (M.op X0 X0) X1)) ∨ (M.op X1 (M.op (M.op X0 X0) X1)) = (k (M.op (M.op X0 X0) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3635 X0 X1 X1 (M.op (M.op X0 X0) X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635
  have eq953971 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (k (M.op (M.op X0 X0) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq953970 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953970
  have eq953974 : ∀ X1 : G, (M.op X1 (M.op (τ x) X1)) = (k (M.op (τ x) X1) X1) := by
    intro X1
    first
    | (have i₁ := eq953971 x X1
       have i₂ := eq115384 x X1
       grind)
    | exact superpose eq115384 eq953971
    | exact resolve eq953971 eq115384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115384 eq953971
  have eq953982 : ∀ X1 : G, (M.op X1 (M.op x X1)) = (k (M.op x X1) X1) := by
    intro X1
    first
    | (have i₁ := eq953974 X1
       have i₂ := eq115725 X1
       grind)
    | exact superpose eq115725 eq953974
    | exact resolve eq953974 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115725 eq953974
  have eq953990 : ∀ X1 : G, (M.op (τ x) x) = (k (M.op x X1) X1) := by
    intro X1
    first
    | (have i₁ := eq953982 X1
       have i₂ := eq115383 X1 x
       grind)
    | exact superpose eq115383 eq953982
    | exact resolve eq953982 eq115383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115383 eq953982
  have eq953992 : ∀ X1 : G, x = (k (M.op x X1) X1) := by
    intro X1
    first
    | (have i₁ := eq953990 X1
       have i₂ := eq115606
       grind)
    | exact superpose eq115606 eq953990
    | exact resolve eq953990 eq115606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115606 eq953990
  have eq954133 : ∀ X0 : G, (τ x) = (k (τ (M.op x (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op x (σ X0)) X0
       have i₂ := eq953992 (σ X0)
       grind)
    | exact superpose eq953992 eq22
    | exact resolve eq22 eq953992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq954140 : ∀ X0 : G, (σ x) = (k (σ (M.op x (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op x (τ X0))
       have i₂ := eq953992 (τ X0)
       grind)
    | exact superpose eq953992 eq18
    | exact resolve eq18 eq953992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq953992
  have eq954149 : ∀ X0 : G, x = (k (σ (M.op x (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq954140 X0
       have i₂ := eq127631
       grind)
    | exact superpose eq127631 eq954140
    | exact resolve eq954140 eq127631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127631 eq954140
  have eq954156 : ∀ X0 : G, x = (k (τ (M.op x (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq954133 X0
       have i₂ := eq115780
       grind)
    | exact superpose eq115780 eq954133
    | exact resolve eq954133 eq115780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115780 eq954133
  have eq962395 : ∀ X0 : G, (k X0 x) = X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq951960 X0
       have i₂ := eq115471 X0
       grind)
    | exact superpose eq115471 eq951960
    | (have j1 := eq115471 X0
       grind)
    | exact resolve eq951960 eq115471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115471 eq951960
  have eq962468 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq962395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962395
  have eq967268 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1975 X0 x X1 X2
       have i₂ := eq962468 X0
       grind)
    | exact superpose eq962468 eq1975
    | (have j0 := eq1975 X2 X1 X1 X2
       grind)
    | exact resolve eq1975 eq962468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975 eq962468
  have eq967311 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq967268 X0 X1 X2
       have j1 := eq952197 X0 X1 X2
       grind)
    | (have r₁ := eq967268 X1 X1 X2
       have r₂ := eq952197 X1 X2 x
       grind)
    | exact resolve eq967268 eq952197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952197 eq967268
  have eq1504598 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq967311 (τ X0) X1 X2
       grind)
    | exact superpose eq967311 eq17
    | (have j1 := eq967311 X0 X1 X2
       grind)
    | exact resolve eq17 eq967311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq967311
  have eq1504641 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1504598 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1504598
    | (have j0 := eq1504598 X0 X1 X2
       grind)
    | exact resolve eq1504598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504598
  have eq2078442 : ∀ X0 : G, (τ (M.op x X0)) = (M.op x (τ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq500186 X0
       have i₂ := eq224317 X0
       grind)
    | exact superpose eq224317 eq500186
    | exact resolve eq500186 eq224317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224317 eq500186
  have eq2810658 : ∀ X0 X1 : G, x = (σ (M.op x (τ (σ X0)))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq954149 (σ X0)
       have i₂ := eq1504641 (σ (M.op x (τ (σ X0)))) X0 X1
       grind)
    | exact superpose eq1504641 eq954149
    | (have j1 := eq1504641 X0 X0 X1
       grind)
    | exact resolve eq954149 eq1504641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954149 eq1504641
  have eq2810686 : ∀ X0 X1 : G, x = (σ (M.op x X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2810658 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2810658
    | (have j0 := eq2810658 X0 X1
       grind)
    | exact resolve eq2810658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810658
  have eq2836980 : ∀ X0 : G, x ≠ (M.op x (σ y)) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq138633
       have i₂ := eq2810686 y X0
       grind)
    | exact superpose eq2810686 eq138633
    | (have j1 := eq2810686 y X0
       grind)
    | exact resolve eq138633 eq2810686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810686
  have eq2837030 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2836980 X0
       have j1 := eq208956 y X0
       grind)
    | (have r₁ := eq2836980 X0
       have r₂ := eq208956 y x
       grind)
    | exact resolve eq2836980 eq208956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208956 eq2836980
  have eq2837595 : x = (M.op y (τ (M.op x (σ y)))) := by
    first
    | (have i₁ := eq954156 y
       have i₂ := eq2837030 (τ (M.op x (σ y)))
       grind)
    | exact superpose eq2837030 eq954156
    | exact resolve eq954156 eq2837030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954156 eq2837030
  have eq2839187 : (M.op x (M.op x y)) = (M.op x (τ (M.op x (σ y)))) := by
    first
    | (have i₁ := eq182678 y (τ (M.op x (σ y)))
       have i₂ := eq2837595
       grind)
    | exact superpose eq2837595 eq182678
    | exact resolve eq182678 eq2837595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182678 eq2837595
  have eq2839374 : (τ (M.op x (σ y))) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2839187
       have i₂ := eq2078442 (σ y)
       grind)
    | exact superpose eq2078442 eq2839187
    | exact resolve eq2839187 eq2078442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078442 eq2839187
  have eq2839494 : (M.op x y) = (τ (M.op x (σ y))) := by
    first
    | (have i₁ := eq2839374
       have i₂ := eq126792 y
       grind)
    | (have i₁ := eq2839374
       have i₂ := eq126792 (M.op x y)
       grind)
    | exact superpose eq126792 eq2839374
    | exact resolve eq2839374 eq126792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126792 eq2839374
  have eq2841089 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq11 (M.op x (σ y))
       have i₂ := eq2839494
       grind)
    | exact superpose eq2839494 eq11
    | exact resolve eq11 eq2839494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839494
  have eq2841100 : False := by grind
  exact eq2841100

/-- `Equation4470`: `x ◇ (y ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_x_pxy_Equation4470 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4470 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4470.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
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
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq61 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq80 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq83 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X1) X2) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq69 X0 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq69 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq93 (σ X0)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq105
    | exact resolve eq105 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq105
  have eq166 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X1
       have i₂ := eq14 (σ X1) X0
       grind)
    | (have i₁ := eq114 X0
       have i₂ := eq14 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq14 eq114
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq9
    | exact resolve eq9 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq166 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq12 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq166 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq166 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq209 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X0) X2) = (k (M.op X0 X0) X2) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) X2
       have i₂ := eq83 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 (M.op X0 X0) X2
       have j1 := eq83 X2 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq83 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq351 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X1 (σ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq168
    | exact resolve eq168 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq611 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq612 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq612 (σ X0) (σ X1)
       grind)
    | exact superpose eq612 eq15
    | (have j1 := eq612 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq632
    | (have j0 := eq632 X0 X1
       grind)
    | exact resolve eq632 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq3315 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq180 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq180 (σ X0) X1
       grind)
    | exact superpose eq180 eq10
    | (have j1 := eq180 X0 X1
       grind)
    | exact resolve eq10 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq11754 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3315 (σ X1) X0
       grind)
    | exact superpose eq3315 eq15
    | (have j1 := eq3315 (σ X1) X0
       grind)
    | exact resolve eq15 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq11790 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11754 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11754
    | (have j0 := eq11754 X0 X1
       grind)
    | exact resolve eq11754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11754
  have eq19022 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11790 x y
       grind)
    | exact superpose eq11790 eq16
    | (have j1 := eq11790 x y
       grind)
    | exact resolve eq16 eq11790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11790
  have eq20383 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19022
       have i₂ := eq612 x y
       grind)
    | exact superpose eq612 eq19022
    | (have j1 := eq612 x y
       grind)
    | exact resolve eq19022 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq19022
  have eq20391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq20383
  have eq20392 : y = (M.op x x) := by grind
  clear eq20391
  have eq21126 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq9 x X0
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq9
    | exact resolve eq9 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21156 : ∀ X0 : G, (M.op (σ x) (σ (M.op X0 X0))) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq351 x X0
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq351
    | exact resolve eq351 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq22141 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq21126 x
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq21126
    | exact resolve eq21126 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21126
  have eq45638 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq21156 x
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq21156
    | exact resolve eq21156 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56330 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq209 x x x
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq209
    | exact resolve eq209 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq56335 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have j0 := eq56330 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56330
  have eq56370 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq56335 X0
       have i₂ := eq22141
       grind)
    | exact superpose eq22141 eq56335
    | (have j0 := eq56335 X0
       grind)
    | exact resolve eq56335 eq22141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56335
  have eq73543 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq56370
  have eq73546 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq73543
       have r₂ := eq22141
       grind)
    | exact resolve eq73543 eq22141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22141 eq73543
  have eq123012 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq45638
       have i₂ := eq672 y x
       grind)
    | exact superpose eq672 eq45638
    | (have j1 := eq672 y x
       grind)
    | exact resolve eq45638 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq45638
  have eq123113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq123012
       have i₂ := eq73546
       grind)
    | exact superpose eq73546 eq123012
    | exact resolve eq123012 eq73546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73546 eq123012
  have eq123172 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq123113
       have r₂ := eq16
       grind)
    | exact resolve eq123113 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123113
  have eq123220 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21156 y
       have i₂ := eq123172
       grind)
    | exact superpose eq123172 eq21156
    | exact resolve eq21156 eq123172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21156
  have eq123307 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq123220
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq123220
    | exact resolve eq123220 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123220
  have eq123317 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq123307
       have i₂ := eq123172
       grind)
    | exact superpose eq123172 eq123307
    | exact resolve eq123307 eq123172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123172 eq123307
  have eq123325 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq123317
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq123317
    | exact resolve eq123317 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123317
  have eq123326 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq123325
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq123325
    | exact resolve eq123325 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123325
  have eq123649 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq123326
       grind)
    | exact superpose eq123326 eq16
    | exact resolve eq16 eq123326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123656 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq123326
       grind)
    | exact superpose eq123326 eq10
    | exact resolve eq10 eq123326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123749 : x = y := by
    first
    | (have i₁ := eq123656
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq123656
    | exact resolve eq123656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123656
  have eq123751 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq123649
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq123649
    | exact resolve eq123649 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq123649
  have eq123764 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq123751
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq123751
    | exact resolve eq123751 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123751
  have eq123776 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq123764
       have i₂ := eq123326
       grind)
    | exact superpose eq123326 eq123764
    | exact resolve eq123764 eq123326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123764
  have eq123780 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq123776
       have i₂ := eq123749
       grind)
    | exact superpose eq123749 eq123776
    | exact resolve eq123776 eq123749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123749 eq123776
  have eq123782 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq123780
       have i₂ := eq20392
       grind)
    | exact superpose eq20392 eq123780
    | exact resolve eq123780 eq20392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20392 eq123780
  have eq123783 : False := by grind
  exact eq123783

/-- `Equation4470`: `x ◇ (y ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation4470 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4470 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4470.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
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
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X1) X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq61 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq80 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq83 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X1) X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq69 X0 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq69 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq93 (σ X0)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq105
    | exact resolve eq105 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq105
  have eq166 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X1
       have i₂ := eq14 (σ X1) X0
       grind)
    | (have i₁ := eq114 X0
       have i₂ := eq14 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq14 eq114
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq9
    | exact resolve eq9 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq166 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq12 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq166 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq166 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq209 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k (M.op X0 X0) X2) = (M.op X2 (M.op X0 X0)) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) X2
       have i₂ := eq83 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 (M.op X0 X0) X2
       have j1 := eq83 X2 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq83 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq351 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X1 (σ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq168
    | exact resolve eq168 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq610 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq611 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq610 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq631 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq611 (σ X1) (σ X0)
       grind)
    | exact superpose eq611 eq15
    | (have j1 := eq611 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 X1
       have i₂ := eq114 X1
       grind)
    | exact superpose eq114 eq631
    | (have j0 := eq631 X0 X1
       grind)
    | exact resolve eq631 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq3309 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq180 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq180 (σ X0) X1
       grind)
    | exact superpose eq180 eq10
    | (have j1 := eq180 X0 X1
       grind)
    | exact resolve eq10 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq11694 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (τ (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3309 (σ X0) X1
       grind)
    | exact superpose eq3309 eq15
    | (have j1 := eq3309 (σ X0) X1
       grind)
    | exact resolve eq15 eq3309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq11730 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11694 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11694
    | (have j0 := eq11694 X0 X1
       grind)
    | exact resolve eq11694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11694
  have eq18957 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11730 x y
       grind)
    | exact superpose eq11730 eq16
    | (have j1 := eq11730 x y
       grind)
    | exact resolve eq16 eq11730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11730
  have eq20321 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18957
       have i₂ := eq611 y x
       grind)
    | exact superpose eq611 eq18957
    | (have j1 := eq611 y x
       grind)
    | exact resolve eq18957 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq18957
  have eq20329 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq20321
  have eq20330 : x = (M.op y y) := by grind
  clear eq20329
  have eq21064 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq20330
       grind)
    | exact superpose eq20330 eq9
    | exact resolve eq9 eq20330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21094 : ∀ X0 : G, (M.op (σ y) (σ (M.op X0 X0))) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq351 y X0
       have i₂ := eq20330
       grind)
    | exact superpose eq20330 eq351
    | exact resolve eq351 eq20330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq22409 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq21064 y
       have i₂ := eq20330
       grind)
    | exact superpose eq20330 eq21064
    | exact resolve eq21064 eq20330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46604 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq21094 y
       have i₂ := eq20330
       grind)
    | exact superpose eq20330 eq21094
    | exact resolve eq21094 eq20330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21094
  have eq55628 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) ∨ (M.op y x) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq209 y y x
       have i₂ := eq20330
       grind)
    | exact superpose eq20330 eq209
    | exact resolve eq209 eq20330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq55630 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ (M.op y x) = (k x y) := by
    intro X0
    first
    | (have j0 := eq55628 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55628
  have eq55662 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq55630 X0
       have i₂ := eq22409
       grind)
    | exact superpose eq22409 eq55630
    | (have j0 := eq55630 X0
       grind)
    | exact resolve eq55630 eq22409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55630
  have eq73162 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by grind
  clear eq55662
  have eq73165 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq73162
       have r₂ := eq22409
       grind)
    | exact resolve eq73162 eq22409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22409 eq73162
  have eq121813 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq46604
       have i₂ := eq671 y x
       grind)
    | exact superpose eq671 eq46604
    | (have j1 := eq671 y x
       grind)
    | exact resolve eq46604 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq46604
  have eq121914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq121813
       have i₂ := eq73165
       grind)
    | exact superpose eq73165 eq121813
    | exact resolve eq121813 eq73165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73165 eq121813
  have eq121968 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq121914
       have r₂ := eq16
       grind)
    | exact resolve eq121914 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121914
  have eq122019 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq121968
       grind)
    | exact superpose eq121968 eq10
    | exact resolve eq10 eq121968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121968
  have eq122100 : y = (M.op x x) := by
    first
    | (have i₁ := eq122019
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq122019
    | exact resolve eq122019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122019
  have eq122272 : y = (M.op y y) := by
    first
    | (have i₁ := eq21064 x
       have i₂ := eq122100
       grind)
    | exact superpose eq122100 eq21064
    | exact resolve eq21064 eq122100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21064 eq122100
  have eq122317 : x = y := by
    first
    | (have i₁ := eq122272
       have i₂ := eq20330
       grind)
    | exact superpose eq20330 eq122272
    | exact resolve eq122272 eq20330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20330 eq122272
  have eq122456 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq122317
       grind)
    | exact superpose eq122317 eq16
    | exact resolve eq16 eq122317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122317
  have eq122507 : False := by grind
  exact eq122507

/-- `Equation4497`: `x ◇ (y ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_x_pxy_Equation4497 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4497 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4497.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) X3
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq9 X2 (M.op X0 X0) X3
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X1 x X3
       have i₂ := eq9 X1 x X0
       grind)
    | (have i₁ := eq9 (M.op x x) X1 x
       have i₂ := eq9 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X1)
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq9 X2 X3 (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq9 X0 X2 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 X2
       have i₂ := eq9 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
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
  have eq92 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq75 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq94 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq92 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq92 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq94 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X2 X3 (M.op X1 X1)
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq26 X2 X3 (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq112 (σ X0)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq112 (τ X0)
       grind)
    | exact superpose eq112 eq19
    | exact resolve eq19 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq163 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq162 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq162
    | exact resolve eq162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq167 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq158 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq158
    | exact resolve eq158 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq169 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq163 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq163
    | exact resolve eq163 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq198 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 X2 X3 (M.op X1 X1)
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq30 X2 X3 (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 (τ X0)
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq112
    | exact resolve eq112 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq247 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq245 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq245
    | exact resolve eq245 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq245
  have eq285 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) = (M.op X0 (M.op (M.op X4 X4) (M.op X5 X5))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq25 X4 X5 X0 x
       have i₂ := eq25 X1 X2 X0 x
       grind)
    | (have i₁ := eq25 X0 X1 (M.op (M.op X0 X0) (M.op X1 X1)) x
       have i₂ := eq25 X0 X1 (M.op x x) x
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op X3 X3)) X4 X1
       have i₂ := eq25 X2 X3 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq9 X2 X1 X3
       have i₂ := eq25 X0 X1 X2 X3
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq14 (σ X1) X0
       grind)
    | (have i₁ := eq167 X0
       have i₂ := eq14 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq14 eq167
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq167 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (σ X0) X2
       have i₂ := eq167 X0
       grind)
    | exact superpose eq167 eq9
    | exact resolve eq9 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq396 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq377 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq377 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq12 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq377 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq377 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq510 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 X4) (M.op X5 X5))) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 X4 X5 X3 (M.op X2 X2)
       have i₂ := eq29 X0 X1 (M.op X2 X2) X2
       grind)
    | (have i₁ := eq25 X4 X5 X3 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq29 X0 X1 (M.op (M.op X0 X0) (M.op X1 X1)) X2
       grind)
    | exact superpose eq29 eq25
    | exact resolve eq25 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29
  have eq702 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (τ X0) X2
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq9
    | exact resolve eq9 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (τ X0)
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq9
    | exact resolve eq9 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X1 X2 (τ X0)
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq26
    | exact resolve eq26 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq717 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X2 (τ X0)
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq30
    | exact resolve eq30 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1857 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1858 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq2243 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op X2 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 (τ X0) X2 X1
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq702
    | exact resolve eq702 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq2674 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (τ (τ (M.op X0 X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq703 (τ X0) X1 X2
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq703
    | exact resolve eq703 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq3336 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (τ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq712 (τ X0) X1 X2
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq712
    | exact resolve eq712 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4075 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq717 (τ X0) X1 X2
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq717
    | exact resolve eq717 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14613 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op X2 (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2243 (τ X0) X1 X2
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq2243
    | exact resolve eq2243 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17132 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (τ (τ (M.op X0 X0)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3336 (τ X0) X1 X2
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq3336
    | exact resolve eq3336 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq18772 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4075 (τ X0) X1 X2
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq4075
    | exact resolve eq4075 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq99618 : ∀ X0 X1 : G, (M.op X1 X1) = (τ X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq396 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq396 (σ X0) X1
       grind)
    | exact superpose eq396 eq10
    | (have j1 := eq396 X0 X1
       grind)
    | exact resolve eq10 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120690 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99618 (σ X1) X0
       grind)
    | exact superpose eq99618 eq15
    | (have j1 := eq99618 (σ X1) X0
       grind)
    | exact resolve eq15 eq99618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99618
  have eq120726 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq120690 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq120690
    | (have j0 := eq120690 X0 X1
       grind)
    | exact resolve eq120690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120690
  have eq167615 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120726 x y
       grind)
    | exact superpose eq120726 eq16
    | (have j1 := eq120726 x y
       grind)
    | exact resolve eq16 eq120726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120726
  have eq172422 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167615
       have i₂ := eq1858 x y
       grind)
    | exact superpose eq1858 eq167615
    | (have j1 := eq1858 x y
       grind)
    | exact resolve eq167615 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq167615
  have eq172430 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq172422
  have eq172431 : y = (M.op x x) := by grind
  clear eq172430
  have eq176058 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq9
    | exact resolve eq9 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176093 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X2 X2) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 X2 x X0 X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq130
    | exact resolve eq130 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176094 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 x X2 X0 X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq130
    | exact resolve eq130 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq176097 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X1) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 X1 x X0 X2
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq198
    | exact resolve eq198 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq176114 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) = (M.op X0 (M.op (M.op X3 X3) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq285 X0 X1 X2 X3 x
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq285
    | exact resolve eq285 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq176151 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X3)) = (M.op y (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq368 x X0 X1 X2 X3
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq368
    | exact resolve eq368 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq176160 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq379 x X1 X0
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq379
    | exact resolve eq379 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq176224 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (τ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq712 x X0 X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq712
    | exact resolve eq712 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq176225 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq717 x X0 X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq717
    | exact resolve eq717 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq176269 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (τ (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2243 x X0 X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq2243
    | exact resolve eq2243 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq176273 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (τ (τ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2674 x X0 X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq2674
    | exact resolve eq2674 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq176310 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (τ (τ (τ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18772 x X0 X1
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq18772
    | exact resolve eq18772 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18772
  have eq176383 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X3)) = (M.op y (τ y)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq176151 x X1 X2 X3
       have i₂ := eq176225 y x
       grind)
    | exact superpose eq176225 eq176151
    | exact resolve eq176151 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176151
  have eq176420 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176114 X0 X1 X2 x
       have i₂ := eq176269 x y
       grind)
    | exact superpose eq176269 eq176114
    | exact resolve eq176114 eq176269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176114
  have eq176434 : ∀ X0 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq176097 X0 x X2
       have i₂ := eq176269 x y
       grind)
    | exact superpose eq176269 eq176097
    | exact resolve eq176097 eq176269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176097
  have eq176435 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (τ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq176094 X0 X1 x
       have i₂ := eq176225 y x
       grind)
    | exact superpose eq176225 eq176094
    | exact resolve eq176094 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176094
  have eq176436 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq176093 X0 X1 x
       have i₂ := eq176269 x y
       grind)
    | exact superpose eq176269 eq176093
    | exact resolve eq176093 eq176269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176093
  have eq176516 : ∀ X1 X2 : G, (M.op y (τ y)) = (M.op (τ (τ y)) (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq176383 X1 X2 x
       have i₂ := eq176273 (M.op (M.op X1 X1) (M.op X2 X2)) x
       grind)
    | exact superpose eq176273 eq176383
    | exact resolve eq176383 eq176273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176383
  have eq176553 : ∀ X0 X2 : G, (M.op X0 (M.op y (τ (τ y)))) = (M.op X0 (M.op (τ y) (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq176420 X0 x X2
       have i₂ := eq176224 x (M.op X2 X2)
       grind)
    | exact superpose eq176224 eq176420
    | exact resolve eq176420 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176420
  have eq176567 : ∀ X0 : G, (M.op X0 (τ y)) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq176434 X0 x
       have i₂ := eq176225 X0 x
       grind)
    | exact superpose eq176225 eq176434
    | exact resolve eq176434 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176434
  have eq176568 : ∀ X1 : G, (M.op (τ y) X1) = (M.op (M.op y (τ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq176435 x X1
       have i₂ := eq176224 x X1
       grind)
    | exact superpose eq176224 eq176435
    | exact resolve eq176435 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176435
  have eq176569 : ∀ X1 : G, (M.op (τ y) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X1
    first
    | (have i₁ := eq176436 x X1
       have i₂ := eq176224 x X1
       grind)
    | exact superpose eq176224 eq176436
    | exact resolve eq176436 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176436
  have eq176634 : ∀ X2 : G, (M.op y (τ y)) = (M.op (τ (τ y)) (M.op (τ y) (M.op X2 X2))) := by
    intro X2
    first
    | (have i₁ := eq176516 x X2
       have i₂ := eq176224 x (M.op X2 X2)
       grind)
    | exact superpose eq176224 eq176516
    | exact resolve eq176516 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176516
  have eq176671 : ∀ X0 : G, (M.op X0 (M.op y (τ (τ y)))) = (M.op X0 (M.op (τ y) (τ y))) := by
    intro X0
    first
    | (have i₁ := eq176553 X0 x
       have i₂ := eq176225 (τ y) x
       grind)
    | exact superpose eq176225 eq176553
    | exact resolve eq176553 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176553
  have eq176731 : (M.op y (τ y)) = (M.op (τ (τ y)) (M.op (τ y) (τ y))) := by
    first
    | (have i₁ := eq176634 x
       have i₂ := eq176225 (τ y) x
       grind)
    | exact superpose eq176225 eq176634
    | exact resolve eq176634 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176634
  have eq176768 : ∀ X0 : G, (M.op X0 (τ (τ (τ y)))) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq176671 X0
       have i₂ := eq176310 X0 (τ y)
       grind)
    | exact superpose eq176310 eq176671
    | exact resolve eq176671 eq176310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176671
  have eq176818 : (M.op y (τ y)) = (M.op (τ (τ y)) (τ (τ (τ y)))) := by
    first
    | (have i₁ := eq176731
       have i₂ := eq176310 (τ (τ y)) (τ y)
       grind)
    | exact superpose eq176310 eq176731
    | exact resolve eq176731 eq176310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176731
  have eq176835 : ∀ X0 : G, (M.op X0 (τ y)) = (M.op X0 (τ (τ (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq176768 X0
       have i₂ := eq176567 X0
       grind)
    | exact superpose eq176567 eq176768
    | exact resolve eq176768 eq176567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176567 eq176768
  have eq200596 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (M.op (M.op X3 X3) (M.op X4 X4)))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq396 X5 (M.op (M.op X3 X3) (M.op X4 X4))
       have i₂ := eq510 X0 X1 X2 (M.op (M.op X3 X3) (M.op X4 X4)) X3 X4
       grind)
    | (have i₁ := eq396 X0 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))
       have i₂ := eq510 X0 X1 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) X4 X5
       grind)
    | exact superpose eq510 eq396
    | (have j0 := eq396 X5 (M.op (M.op X3 X3) (M.op X4 X4))
       grind)
    | exact resolve eq396 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq510
  have eq202312 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (M.op (τ y) (M.op X4 X4)))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq200596 X0 X1 X2 X3 X4 X5
       have i₂ := eq176224 X3 (M.op X4 X4)
       grind)
    | exact superpose eq176224 eq200596
    | (have j0 := eq200596 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq200596 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200596
  have eq204136 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (M.op (τ y) (τ y)))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq202312 X0 X1 X2 X3 X4 X5
       have i₂ := eq176225 (τ y) X4
       grind)
    | exact superpose eq176225 eq202312
    | (have j0 := eq202312 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq202312 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202312
  have eq205655 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (τ (τ (τ y))))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq204136 X0 X1 X2 X3 X4 X5
       have i₂ := eq176310 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (τ y)
       grind)
    | exact superpose eq176310 eq204136
    | (have j0 := eq204136 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq204136 eq176310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204136
  have eq207074 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (τ y))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq205655 X0 X1 X2 X3 X4 X5
       have i₂ := eq176835 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))
       grind)
    | exact superpose eq176835 eq205655
    | (have j0 := eq205655 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq205655 eq176835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176835 eq205655
  have eq208491 : ∀ X0 X1 X3 X4 X5 : G, (σ (M.op (M.op (τ (τ y)) (M.op (M.op X0 X0) (M.op X1 X1))) (τ y))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq207074 X0 X1 x X3 X4 X5
       have i₂ := eq176273 (M.op (M.op X0 X0) (M.op X1 X1)) x
       grind)
    | exact superpose eq176273 eq207074
    | (have j0 := eq207074 X0 X1 x X3 X4 X5
       grind)
    | exact resolve eq207074 eq176273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176273 eq207074
  have eq209902 : ∀ X1 X3 X4 X5 : G, (σ (M.op (M.op (τ (τ y)) (M.op (τ y) (M.op X1 X1))) (τ y))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq208491 x X1 X3 X4 X5
       have i₂ := eq176224 x (M.op X1 X1)
       grind)
    | exact superpose eq176224 eq208491
    | (have j0 := eq208491 x X1 X3 X4 X5
       grind)
    | exact resolve eq208491 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208491
  have eq211301 : ∀ X3 X4 X5 : G, (σ (M.op (M.op (τ (τ y)) (M.op (τ y) (τ y))) (τ y))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq209902 x X3 X4 X5
       have i₂ := eq176225 (τ y) x
       grind)
    | exact superpose eq176225 eq209902
    | (have j0 := eq209902 x X3 X4 X5
       grind)
    | exact resolve eq209902 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209902
  have eq212669 : ∀ X3 X4 X5 : G, (σ (M.op (M.op (τ (τ y)) (τ (τ (τ y)))) (τ y))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq211301 X3 X4 X5
       have i₂ := eq176310 (τ (τ y)) (τ y)
       grind)
    | exact superpose eq176310 eq211301
    | (have j0 := eq211301 X3 X4 X5
       grind)
    | exact resolve eq211301 eq176310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176310 eq211301
  have eq213901 : ∀ X3 X4 X5 : G, (σ (M.op (M.op y (τ y)) (τ y))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq212669 X3 X4 X5
       have i₂ := eq176818
       grind)
    | exact superpose eq176818 eq212669
    | (have j0 := eq212669 X3 X4 X5
       grind)
    | exact resolve eq212669 eq176818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176818 eq212669
  have eq214925 : ∀ X3 X4 X5 : G, (σ (M.op (τ y) (τ y))) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq213901 X3 X4 X5
       have i₂ := eq176568 (τ y)
       grind)
    | exact superpose eq176568 eq213901
    | (have j0 := eq213901 X3 X4 X5
       grind)
    | exact resolve eq213901 eq176568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176568 eq213901
  have eq215774 : ∀ X3 X4 X5 : G, (M.op y y) = X5 ∨ (k (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) = (M.op (σ (M.op (M.op X3 X3) (M.op X4 X4))) X5) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq214925 X3 X4 X5
       have i₂ := eq169 y
       grind)
    | exact superpose eq169 eq214925
    | (have j0 := eq214925 X3 X4 X5
       grind)
    | exact resolve eq214925 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214925
  have eq216479 : ∀ X4 X5 : G, (k (σ (M.op (τ y) (M.op X4 X4))) X5) = (M.op (σ (M.op (τ y) (M.op X4 X4))) X5) ∨ (M.op y y) = X5 := by
    intro X4 X5
    first
    | (have i₁ := eq215774 x X4 X5
       have i₂ := eq176224 x (M.op X4 X4)
       grind)
    | exact superpose eq176224 eq215774
    | (have j0 := eq215774 x X4 X5
       grind)
    | exact resolve eq215774 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215774
  have eq217041 : ∀ X5 : G, (M.op (σ (M.op (τ y) (τ y))) X5) = (k (σ (M.op (τ y) (τ y))) X5) ∨ (M.op y y) = X5 := by
    intro X5
    first
    | (have i₁ := eq216479 x X5
       have i₂ := eq176225 (τ y) x
       grind)
    | exact superpose eq176225 eq216479
    | (have j0 := eq216479 x X5
       grind)
    | exact resolve eq216479 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216479
  have eq217511 : ∀ X5 : G, (M.op (M.op y y) X5) = (k (M.op y y) X5) ∨ (M.op y y) = X5 := by
    intro X5
    first
    | (have i₁ := eq217041 X5
       have i₂ := eq169 y
       grind)
    | exact superpose eq169 eq217041
    | (have j0 := eq217041 X5
       grind)
    | exact resolve eq217041 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq217041
  have eq217923 : ∀ X5 : G, (M.op (M.op y y) X5) = (k (M.op y y) X5) := by
    intro X5
    first
    | (have j0 := eq217511 X5
       have j1 := eq94 (M.op y y) X5
       grind)
    | (have r₁ := eq217511 X5
       have r₂ := eq94 (M.op (M.op y y) X5) (k (M.op y y) X5)
       grind)
    | (have r₁ := eq217511 X5
       have r₂ := eq94 (k (M.op y y) X5) (M.op (M.op y y) X5)
       grind)
    | (have r₁ := eq217511 x
       have r₂ := eq94 (M.op y y) x
       grind)
    | exact resolve eq217511 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq217511
  have eq218297 : ∀ X5 : G, (M.op (τ y) X5) = (k (M.op y y) X5) := by
    intro X5
    first
    | (have i₁ := eq217923 X5
       have i₂ := eq176224 y X5
       grind)
    | exact superpose eq176224 eq217923
    | exact resolve eq217923 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217923
  have eq235846 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq176058 X0 x
       have i₂ := eq172431
       grind)
    | exact superpose eq172431 eq176058
    | exact resolve eq176058 eq172431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172431
  have eq236111 : ∀ X0 X2 : G, (M.op (τ (τ (τ (M.op X2 X2)))) X0) = (M.op X0 y) := by
    intro X0 X2
    first
    | (have i₁ := eq17132 X2 x X0
       have i₂ := eq176058 X0 x
       grind)
    | exact superpose eq176058 eq17132
    | exact resolve eq17132 eq176058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236578 : ∀ X0 X1 X2 : G, (M.op (τ (τ (τ (M.op X2 X2)))) X1) = (M.op (M.op (M.op X0 X0) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17132 X2 (M.op X0 X0) X1
       have i₂ := eq176058 (M.op X0 X0) X0
       grind)
    | exact superpose eq176058 eq17132
    | exact resolve eq17132 eq176058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17132
  have eq236730 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (τ (τ (τ (M.op X0 X0)))) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14613 X0 X1 (M.op X2 X2)
       have i₂ := eq176058 (τ (τ (τ (M.op X0 X0)))) X2
       grind)
    | exact superpose eq176058 eq14613
    | exact resolve eq14613 eq176058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14613
  have eq236732 : ∀ X0 X2 : G, (M.op (τ y) (M.op X2 X2)) = (M.op (τ (τ (τ (M.op X0 X0)))) y) := by
    intro X0 X2
    first
    | (have i₁ := eq236730 X0 x X2
       have i₂ := eq176224 x (M.op X2 X2)
       grind)
    | exact superpose eq176224 eq236730
    | exact resolve eq236730 eq176224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176224 eq236730
  have eq236868 : ∀ X1 X2 : G, (M.op (τ (τ (τ (M.op X2 X2)))) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq236578 x X1 X2
       have i₂ := eq176269 x y
       grind)
    | exact superpose eq176269 eq236578
    | exact resolve eq236578 eq176269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176269 eq236578
  have eq237720 : ∀ X2 : G, (M.op y y) = (M.op (τ y) (M.op X2 X2)) := by
    intro X2
    first
    | (have i₁ := eq236732 x X2
       have i₂ := eq236111 y x
       grind)
    | exact superpose eq236111 eq236732
    | exact resolve eq236732 eq236111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236732
  have eq237853 : ∀ X1 X2 : G, (M.op (τ (τ (τ (M.op X2 X2)))) X1) = (M.op (τ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq236868 X1 X2
       have i₂ := eq176569 X1
       grind)
    | exact superpose eq176569 eq236868
    | exact resolve eq236868 eq176569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176569 eq236868
  have eq238649 : (M.op y y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq237720 x
       have i₂ := eq176225 (τ y) x
       grind)
    | exact superpose eq176225 eq237720
    | exact resolve eq237720 eq176225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176225 eq237720
  have eq238770 : ∀ X1 : G, (M.op X1 y) = (M.op (τ y) X1) := by
    intro X1
    first
    | (have i₁ := eq237853 X1 x
       have i₂ := eq236111 X1 x
       grind)
    | exact superpose eq236111 eq237853
    | exact resolve eq237853 eq236111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236111 eq237853
  have eq239389 : (M.op y y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq238649
       have i₂ := eq247 y
       grind)
    | exact superpose eq247 eq238649
    | exact resolve eq238649 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq238649
  have eq355753 : ∀ X0 : G, (k (M.op y y) (σ X0)) = (σ (k (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq18 (M.op y y) X0
       have i₂ := eq239389
       grind)
    | exact superpose eq239389 eq18
    | exact resolve eq18 eq239389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq239389
  have eq355806 : ∀ X0 : G, (σ (M.op (τ y) X0)) = (k (M.op y y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq355753 X0
       have i₂ := eq218297 X0
       grind)
    | exact superpose eq218297 eq355753
    | exact resolve eq355753 eq218297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355753
  have eq355827 : ∀ X0 : G, (M.op (τ y) (σ X0)) = (σ (M.op (τ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq355806 X0
       have i₂ := eq218297 (σ X0)
       grind)
    | exact superpose eq218297 eq355806
    | exact resolve eq355806 eq218297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218297 eq355806
  have eq355844 : ∀ X0 : G, (M.op (τ y) (σ X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq355827 X0
       have i₂ := eq238770 X0
       grind)
    | (have i₁ := eq355827 y
       have i₂ := eq238770 (τ y)
       grind)
    | exact superpose eq238770 eq355827
    | exact resolve eq355827 eq238770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355827
  have eq355852 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq355844 X0
       have i₂ := eq238770 (σ X0)
       grind)
    | exact superpose eq238770 eq355844
    | exact resolve eq355844 eq238770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238770 eq355844
  have eq355859 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq355852 X0
       have i₂ := eq235846 (σ X0)
       grind)
    | exact superpose eq235846 eq355852
    | exact resolve eq355852 eq235846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355852
  have eq541791 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq176058 X0 x
       have i₂ := eq176160 x X0
       grind)
    | exact superpose eq176160 eq176058
    | exact resolve eq176058 eq176160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176058 eq176160
  have eq547767 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq541791 (σ x)
       grind)
    | exact superpose eq541791 eq16
    | exact resolve eq16 eq541791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541791
  have eq547872 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq547767
       have i₂ := eq235846 (σ x)
       grind)
    | exact superpose eq235846 eq547767
    | exact resolve eq547767 eq235846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235846 eq547767
  have eq548229 : False := by grind
  exact eq548229

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation450 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
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
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq15
    | (have j1 := eq91 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq91 (τ X0) X1
       grind)
    | exact superpose eq91 eq18
    | (have j1 := eq91 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq91
  have eq954 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq258
    | exact resolve eq258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq1000 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq954
    | (have j0 := eq954 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq954 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq2425 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq2647 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2425
       have i₂ := eq1000 x y
       grind)
    | exact superpose eq1000 eq2425
    | (have j1 := eq1000 (σ x) (σ y)
       grind)
    | (have r₁ := eq2425
       have r₂ := eq1000 x y
       grind)
    | (have r₁ := eq2425
       have r₂ := eq1000 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2425
       have r₂ := eq1000 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2425 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq2425
  have eq2648 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2647
  have eq2703 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2648
       grind)
    | exact superpose eq2648 eq10
    | exact resolve eq10 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq2749 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2703
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2703
    | exact resolve eq2703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2750 : x = y := by grind
  clear eq2749
  have eq2941 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2750
       grind)
    | exact superpose eq2750 eq16
    | exact resolve eq16 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq2942 : False := by grind
  exact eq2942

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation450 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq408 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq437 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq408
    | (have j0 := eq408 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq874 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq16
    | (have j1 := eq73 x y
       grind)
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq874
       have i₂ := eq437 x y
       grind)
    | exact superpose eq437 eq874
    | (have j1 := eq437 (σ x) (σ y)
       grind)
    | (have r₁ := eq874
       have r₂ := eq437 x y
       grind)
    | (have r₁ := eq874
       have r₂ := eq437 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq874
       have r₂ := eq437 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq874 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq874
  have eq962 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq961
  have eq1081 : y = (τ (σ x)) ∨ x = y := by
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
  have eq1119 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1081
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1081
    | exact resolve eq1081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1120 : x = y := by grind
  clear eq1119
  have eq1241 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq16
    | exact resolve eq16 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1242 : False := by grind
  exact eq1242

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation450 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
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
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X1 X1 X2
       have j1 := eq54 X1 X1 X2
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
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq117 (σ X0) (σ X1)
       grind)
    | exact superpose eq117 eq15
    | (have j1 := eq117 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq117 (τ X0) X1
       grind)
    | exact superpose eq117 eq18
    | (have j1 := eq117 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq117
  have eq636 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq237 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq237
    | exact resolve eq237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq668 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq636
    | (have j0 := eq636 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq1828 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235 x y
       grind)
    | exact superpose eq235 eq16
    | (have j1 := eq235 x y
       grind)
    | exact resolve eq16 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq1931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1828
       have i₂ := eq668 x y
       grind)
    | exact superpose eq668 eq1828
    | (have j1 := eq668 (σ x) (σ y)
       grind)
    | (have r₁ := eq1828
       have r₂ := eq668 x y
       grind)
    | (have r₁ := eq1828
       have r₂ := eq668 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1828
       have r₂ := eq668 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1828 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq1828
  have eq1932 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1931
  have eq2024 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1932
       grind)
    | exact superpose eq1932 eq10
    | exact resolve eq10 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2067 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2024
    | exact resolve eq2024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2068 : x = y := by grind
  clear eq2067
  have eq2160 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2068
       grind)
    | exact superpose eq2068 eq16
    | exact resolve eq16 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2161 : False := by grind
  exact eq2161
