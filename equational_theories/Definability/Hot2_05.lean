import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4364`: `x ◇ (y ◇ z) = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pyy_pxy_Equation4364 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4364 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4364.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq60 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq60 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq61 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq63 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq63 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq29 X1
       grind)
    | exact superpose eq29 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq64 X1 X0
       grind)
    | (have r₁ := eq78 X1 X0
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq78 X0 X0
       have r₂ := eq64 X0 X0
       grind)
    | exact resolve eq78 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq78
  have eq196 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq203 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq84 X0 X0
       grind)
    | exact resolve eq196 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq196
  have eq953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq203 (σ X0) (σ X1)
       grind)
    | exact superpose eq203 eq15
    | exact resolve eq15 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq203 X0 X1
       grind)
    | exact superpose eq203 eq953
    | exact resolve eq953 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq953
  have eq960 : False := by grind
  exact eq960

/-- `Equation4418`: `x ◇ (x ◇ y) = (z ◇ x) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyy_pxx_pxy_Equation4418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X3) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k (k x X0) X1)) = (k (k (σ x) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k x X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq175 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 (M.op X2 X0)) X5) = (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 (M.op X2 X0) x X4 X5
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X0 x X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X4 X1 (M.op (M.op X1 X2) x)
       have i₂ := eq16 (M.op X1 X2) x X0 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X2 : G, (M.op (M.op x y) X2) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq180 (M.op y x) X2
       have i₂ := eq180 x X0
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq180 x X2
       have i₂ := eq180 x X0
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op X2 y) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 y x X2 X3
       have i₂ := eq180 x X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq217 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X2
    first
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X2 (σ y)) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq243 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X2 (M.op (σ x) (σ y))) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq217 eq16
    | exact resolve eq16 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq275 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq187 eq191
    | exact resolve eq191 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq324 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq187 eq221
    | exact resolve eq221 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq538 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq275 eq16
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq275 eq243
    | exact resolve eq243 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq543 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X1) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X0) = (k X2 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq275 eq13
    | (have r₁ := eq13 X0 (M.op (M.op x y) X1)
       have r₂ := eq275 X1 X1 (M.op (M.op x y) X1)
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (k X2 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq543 X0 X1 X2
       grind)
    | (have r₁ := eq543 X2 X0 X2
       have r₂ := eq187 X0 X2
       grind)
    | (have r₁ := eq543 X0 X2 X2
       have r₂ := eq187 X0 X2
       grind)
    | exact resolve eq543 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq688 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq324 eq16
    | exact resolve eq16 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X1) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X2 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq324 eq13
    | exact resolve eq13 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq701 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X2 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq693 X0 X1 X2
       grind)
    | (have r₁ := eq693 X1 X0 X2
       have r₂ := eq542 X0 X1
       grind)
    | exact resolve eq693 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq766 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq538 (M.op sF0 x) X1 x
       have i₂ := eq538 X0 sF0 x
       grind)
    | exact superpose eq538 eq538
    | exact resolve eq538 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X1) = (M.op X2 (M.op (M.op x y) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 X1 X2 (M.op X2 x)
       have i₂ := eq538 X0 X2 x
       grind)
    | (have i₁ := eq538 X0 (M.op x y) X0
       have i₂ := eq538 X0 X1 X2
       grind)
    | exact superpose eq538 eq538
    | exact resolve eq538 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq538 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq538
    | (have j0 := eq538 X0 x y
       grind)
    | exact resolve eq538 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq538
    | (have j0 := eq538 X0 (σ x) (σ y)
       grind)
    | exact resolve eq538 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 X3 X4 : G, (M.op (M.op x y) X0) = (M.op (M.op X3 X1) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 X1 x X3 X4
       have i₂ := eq538 X0 X1 x
       grind)
    | (have i₁ := eq16 (M.op x y) X1 x X3
       have i₂ := eq538 (M.op (M.op x y) X1) X1 x
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) X1) X2) = (M.op x (M.op x y)) := by
    intro X1 X2
    first
    | exact superpose eq781 eq275
    | exact resolve eq275 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq917 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op x (M.op x y)) := by
    intro X1 X2
    first
    | exact superpose eq781 eq538
    | exact resolve eq538 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq781 eq542
    | exact resolve eq542 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq954 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X1 X2
    first
    | exact superpose eq794 eq538
    | exact resolve eq538 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq794 eq781
    | exact resolve eq781 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X1 X2 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) X2) = (M.op x (M.op x y)) := by
    intro X1 X2
    first
    | exact superpose eq918 eq16
    | exact resolve eq16 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : ∀ X1 X2 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X1 X2
    first
    | exact superpose eq956 eq997
    | exact resolve eq997 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1116 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq551 eq794
    | exact resolve eq794 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : ∀ X0 X1 : G, (k (σ x) (σ (M.op (M.op x y) X1))) = (σ (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq551 eq35
    | exact resolve eq35 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1224 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq11 X0 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X0 X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1238 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1261 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1435 : ∀ X0 X1 : G, (M.op (M.op x y) X1) ≠ (M.op (M.op x y) X0) ∨ y = (M.op y y) ∨ (M.op (M.op (M.op x y) X1) (M.op (M.op x y) X1)) = (k (M.op (M.op x y) X1) y) := by
    intro X0 X1
    first
    | exact superpose eq185 eq12
    | (have j0 := eq12 (M.op (M.op x y) X1) y
       grind)
    | (have r₁ := eq12 (M.op y (M.op (M.op x y) X0)) (M.op x y)
       have r₂ := eq185 X0 (M.op y (M.op (M.op x y) X0))
       grind)
    | (have r₁ := eq12 (M.op (M.op x y) x) y
       have r₂ := eq185 x x
       grind)
    | exact resolve eq12 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1488 : ∀ X1 : G, y = (M.op y y) ∨ (M.op (M.op (M.op x y) X1) (M.op (M.op x y) X1)) = (k (M.op (M.op x y) X1) y) := by
    intro X1
    first
    | (have j0 := eq1435 x X1
       grind)
    | (have r₁ := eq1435 x x
       have r₂ := eq187 x x
       grind)
    | (have r₁ := eq1435 x x
       have r₂ := eq187 x x
       grind)
    | exact resolve eq1435 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq1435
  have eq1516 : ∀ X1 : G, (M.op x (M.op x y)) = (k (M.op (M.op x y) X1) y) ∨ y = (M.op y y) := by
    intro X1
    first
    | exact superpose eq913 eq1488
    | exact resolve eq1488 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq1488
  have eq1533 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (M.op x y) X1) y) ∨ y = (M.op y y) := by
    intro X1
    first
    | exact superpose eq956 eq1516
    | exact resolve eq1516 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq1725 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq688 X3 X1 (M.op X1 x)
       have i₂ := eq688 X0 X1 x
       grind)
    | (have i₁ := eq688 X0 (M.op (σ x) (σ y)) X0
       have i₂ := eq688 X0 X1 x
       grind)
    | exact superpose eq688 eq688
    | exact resolve eq688 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq781 eq688
    | exact resolve eq688 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1758 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (σ x) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq794 eq688
    | exact resolve eq688 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1831 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X3 X1) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 X1 x X3 X4
       have i₂ := eq688 X0 X1 x
       grind)
    | (have i₁ := eq16 (M.op (σ x) (σ y)) X1 x X3
       have i₂ := eq688 (M.op (M.op (σ x) (σ y)) X1) X1 x
       grind)
    | exact superpose eq688 eq16
    | exact resolve eq16 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 X1 (M.op X1 x) X3 X4
       have i₂ := eq688 X0 X1 x
       grind)
    | (have i₁ := eq16 (M.op (σ x) (σ y)) X0 x X3
       have i₂ := eq688 X0 X1 x
       grind)
    | exact superpose eq688 eq16
    | exact resolve eq16 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq1913 : ∀ X1 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X1 (M.op x (M.op x y))) := by
    intro X1 X3 X4
    first
    | exact superpose eq918 eq1836
    | exact resolve eq1836 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1917 : ∀ X1 X3 X4 : G, (M.op x (M.op x y)) = (M.op (M.op X3 X1) X4) := by
    intro X1 X3 X4
    first
    | exact superpose eq918 eq1831
    | exact resolve eq1831 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1925 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq918 eq1758
    | exact resolve eq1758 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1926 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq918 eq1740
    | exact resolve eq1740 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1932 : ∀ X1 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op X1 (M.op x (M.op x y))) := by
    intro X1 X3
    first
    | exact superpose eq918 eq1725
    | exact resolve eq1725 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq1938 : ∀ X1 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1 X3 X4
    first
    | exact superpose eq956 eq1913
    | exact resolve eq1913 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq1942 : ∀ X1 X3 X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X3 X1) X4) := by
    intro X1 X3 X4
    first
    | exact superpose eq956 eq1917
    | exact resolve eq1917 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq1947 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq956 eq1925
    | exact resolve eq1925 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1948 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq956 eq1926
    | exact resolve eq1926 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq1954 : ∀ X1 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1 X3
    first
    | exact superpose eq956 eq1932
    | exact resolve eq1932 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq1963 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq918 eq1954
    | exact resolve eq1954 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq1967 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq956 eq1963
    | exact resolve eq1963 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq4785 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op x X1)
       have i₂ := eq1942 X1 x (M.op x X1)
       grind)
    | exact superpose eq1942 eq13
    | (have r₁ := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq1942 (M.op (σ x) (σ y)) (σ x) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq6676 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (σ x) (σ y)) X0)) = (k X1 (σ (M.op (M.op x y) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq701 eq34
    | exact resolve eq34 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq6677 : ∀ X0 X1 X2 : G, (σ (M.op (M.op x y) X0)) = (k X1 (σ (M.op (M.op x y) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq551 eq34
    | exact resolve eq34 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq6709 : ∀ X1 X2 : G, (σ (M.op x (M.op x y))) = (k X1 (σ (M.op (M.op x y) X2))) := by
    intro X1 X2
    first
    | exact superpose eq918 eq6676
    | exact resolve eq6676 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq6676
  have eq6715 : ∀ X1 X2 : G, (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k X1 (σ (M.op (M.op x y) X2))) := by
    intro X1 X2
    first
    | exact superpose eq956 eq6709
    | exact resolve eq6709 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6709
  have eq6753 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq8128 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1282 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1282
    | (have j0 := eq1282 (σ X0)
       grind)
    | exact resolve eq1282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8179 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6753 (k (τ X0) X1) X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq6753
    | exact resolve eq6753 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37464 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1238
       grind)
    | exact superpose eq1238 eq40
    | exact resolve eq40 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq37465 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37464
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37464
    | exact resolve eq37464 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37464
  have eq37467 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq37465
    | exact resolve eq37465 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37465
  have eq73908 : ∀ X0 X2 : G, (σ (M.op (M.op x y) X0)) = (σ (M.op (M.op x y) X2)) := by
    intro X0 X2
    first
    | exact superpose eq1122 eq1122
    | exact resolve eq1122 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73980 : ∀ X0 X1 X2 : G, (σ (k (M.op (M.op x y) X1) X2)) = (k (k (σ x) (σ (M.op (M.op x y) X0))) (σ X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1122 eq10
    | exact resolve eq10 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73990 : ∀ X0 X1 X2 : G, (k (M.op (M.op x y) X1) (τ X2)) = (τ (k (k (σ x) (σ (M.op (M.op x y) X0))) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1122 eq6753
    | exact resolve eq6753 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq73991 : ∀ X0 X1 X2 : G, (k (M.op (M.op x y) X1) (τ X2)) = (k (k (τ (σ x)) (M.op (M.op x y) X0)) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73990 X0 X1 X2
       have i₂ := eq8179 sF2 (M.op sF0 X0) X2
       grind)
    | exact superpose eq8179 eq73990
    | exact resolve eq73990 eq8179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8179 eq73990
  have eq74001 : ∀ X0 X1 X2 : G, (σ (k (M.op (M.op x y) X1) X2)) = (σ (k (k x (M.op (M.op x y) X0)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq43 eq73980
    | exact resolve eq73980 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq73980
  have eq74117 : ∀ X1 X2 : G, (k (M.op (M.op x y) X1) (τ X2)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ X2)) := by
    intro X1 X2
    first
    | exact superpose eq1116 eq73991
    | exact resolve eq73991 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73991
  have eq74126 : ∀ X1 X2 : G, (σ (k (M.op (M.op x y) X1) X2)) = (σ (k (M.op (σ x) (M.op (σ x) (σ y))) X2)) := by
    intro X1 X2
    first
    | exact superpose eq1116 eq74001
    | exact resolve eq74001 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq74001
  have eq74383 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1967 eq73908
    | exact resolve eq73908 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74406 : ∀ X0 X1 X2 : G, (σ (k (M.op (M.op x y) X1) X2)) = (k (σ (M.op (M.op x y) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq73908 eq10
    | exact resolve eq10 eq73908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74413 : ∀ X0 X1 : G, (k (M.op (M.op x y) X1) y) = (τ (k (σ (M.op (M.op x y) X0)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq73908 eq72
    | exact resolve eq72 eq73908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74420 : ∀ X0 X1 : G, (k (M.op (M.op x y) X1) y) = (k (M.op (M.op x y) X0) y) := by
    intro X0 X1
    first
    | exact superpose eq72 eq74413
    | exact resolve eq74413 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq74413
  have eq74427 : ∀ X0 X1 X2 : G, (σ (k (M.op (M.op x y) X1) X2)) = (σ (k (M.op (M.op x y) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74406 X0 X1 X1
       have i₂ := eq10 (M.op sF0 X0) X1
       grind)
    | exact superpose eq10 eq74406
    | exact resolve eq74406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74406
  have eq77545 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X3) ≠ (M.op X2 (M.op X2 X4)) ∨ (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (M.op (M.op X2 (M.op X2 X4)) (M.op X2 (M.op X2 X4))) = (k (M.op X2 (M.op X2 X4)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 (M.op X2 (M.op X2 X4)) (M.op X1 X2)
       have i₂ := eq175 X2 X4 X1 X0 X3
       grind)
    | exact superpose eq175 eq12
    | (have j0 := eq12 (M.op X2 (M.op X2 X4)) (M.op X1 X2)
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) (M.op X4 (M.op X2 X0))
       have r₂ := eq175 X0 X1 X2 X4 (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1)))
       grind)
    | exact resolve eq12 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq77599 : ∀ X1 X2 X4 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (M.op (M.op X2 (M.op X2 X4)) (M.op X2 (M.op X2 X4))) = (k (M.op X2 (M.op X2 X4)) (M.op X1 X2)) := by
    intro X1 X2 X4
    first
    | (have j0 := eq77545 x X1 X2 x X4
       grind)
    | (have r₁ := eq77545 x X1 X2 x X4
       have r₂ := eq183 x X1 X2 x X4
       grind)
    | exact resolve eq77545 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq77545
  have eq78716 : ∀ X1 X2 X4 : G, (M.op X1 X2) = (M.op X2 (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (M.op X2 (M.op X2 X4)) (M.op X2 (M.op X2 X4))) = (k (M.op X2 (M.op X2 X4)) (M.op X1 X2)) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq77599 X1 X2 X4
       have i₂ := eq1938 X2 X1 (M.op X1 X2)
       grind)
    | exact superpose eq1938 eq77599
    | (have j0 := eq77599 X1 X2 X4
       grind)
    | exact resolve eq77599 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77599
  have eq79621 : ∀ X1 X2 X4 : G, (M.op X1 X2) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (M.op X2 (M.op X2 X4)) (M.op X2 (M.op X2 X4))) = (k (M.op X2 (M.op X2 X4)) (M.op X1 X2)) := by
    intro X1 X2 X4
    first
    | exact superpose eq1967 eq78716
    | (have j0 := eq78716 X1 X2 X4
       grind)
    | exact resolve eq78716 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78716
  have eq79905 : ∀ X1 X2 : G, (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = (k (M.op x (M.op x y)) (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X1 X2
    first
    | (have i₁ := eq79621 X1 X1 X2
       have i₂ := eq917 X1 X2
       grind)
    | (have i₁ := eq79621 X1 x y
       have i₂ := eq917 X1 X2
       grind)
    | exact superpose eq917 eq79621
    | (have j0 := eq79621 X1 X2 x
       grind)
    | exact resolve eq79621 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq79621
  have eq80066 : ∀ X1 X2 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X1 X2
    first
    | exact superpose eq956 eq79905
    | (have j0 := eq79905 X1 X2
       grind)
    | exact resolve eq79905 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79905
  have eq80088 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X1 X2
    first
    | exact superpose eq1002 eq80066
    | (have j0 := eq80066 X1 X2
       grind)
    | exact resolve eq80066 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002 eq80066
  have eq80094 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X2)) := by
    intro X1 X2
    first
    | (have j0 := eq80088 X1 X2
       have j1 := eq4785 X1 X2 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq80088 x X1
       have r₂ := eq4785 x X1 X2
       grind)
    | (have r₁ := eq80088 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq4785 (σ x) (M.op (σ x) (σ y)) X2
       grind)
    | exact resolve eq80088 eq4785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785 eq80088
  have eq80648 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq794 eq80094
    | exact resolve eq80094 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89855 : ∀ X0 X1 : G, (σ (M.op (M.op x y) X1)) ≠ (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X1)) = (M.op (σ (M.op (M.op x y) X1)) (σ (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq6677 eq1282
    | (have j0 := eq1282 (σ (M.op (M.op x y) X1))
       grind)
    | (have r₁ := eq1282 (σ (M.op (M.op x y) X0))
       have r₂ := eq6677 X0 (σ (M.op (M.op x y) X0)) X0
       grind)
    | exact resolve eq1282 eq6677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677
  have eq89883 : ∀ X1 : G, (σ (M.op (M.op x y) X1)) = (M.op (σ (M.op (M.op x y) X1)) (σ (M.op (M.op x y) X1))) := by
    intro X1
    first
    | (have j0 := eq89855 x X1
       grind)
    | (have r₁ := eq89855 x x
       have r₂ := eq73908 x x
       grind)
    | (have r₁ := eq89855 x x
       have r₂ := eq73908 x x
       grind)
    | exact resolve eq89855 eq73908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73908 eq89855
  have eq147171 : ∀ X0 : G, (k X0 (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1224 X0 X0 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq147181 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (k X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq147171 X0
       have i₂ := eq1938 X0 X0 X0
       grind)
    | exact superpose eq1938 eq147171
    | (have j0 := eq147171 X0
       grind)
    | exact resolve eq147171 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147171
  have eq147864 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1967 eq147181
    | (have j0 := eq147181 X0
       grind)
    | exact resolve eq147181 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147181
  have eq148529 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op X0 X0)) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq147864 X0
       have i₂ := eq1938 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1938 eq147864
    | (have j0 := eq147864 X0
       grind)
    | exact resolve eq147864 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938 eq147864
  have eq149082 : ∀ X0 : G, (k X0 (M.op X0 X0)) ≠ X0 ∨ (M.op (σ x) (M.op (σ x) (σ y))) = X0 ∨ (M.op X0 X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1967 eq148529
    | (have j0 := eq148529 X0
       grind)
    | exact resolve eq148529 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148529
  have eq150317 : ∀ X0 X1 : G, (k (M.op (σ x) (M.op (σ x) (σ y))) X0) = (k (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq74117 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq74117
    | exact resolve eq74117 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74117
  have eq150507 : ∀ X0 X1 X2 : G, (k (M.op (M.op x y) X0) X1) = (k (M.op (M.op x y) X2) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq150317 eq150317
    | exact resolve eq150317 eq150317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150636 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (M.op x y) X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq150317 eq80094
    | exact resolve eq80094 eq150317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80094
  have eq150691 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq150317 eq80648
    | exact resolve eq80648 eq150317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150317
  have eq153039 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) X3) = (k (M.op (M.op x y) X0) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq150507 eq80648
    | exact resolve eq80648 eq150507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80648
  have eq198755 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (M.op x y) X1) (σ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq89883 eq150636
    | exact resolve eq150636 eq89883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198757 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X1) = (k (M.op (M.op x y) X2) (σ (M.op (M.op x y) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq89883 eq153039
    | exact resolve eq153039 eq89883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89883 eq153039
  have eq198761 : ∀ X1 : G, (M.op (M.op x y) X1) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq6715 eq198757
    | exact resolve eq198757 eq6715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198757
  have eq198763 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq6715 eq198755
    | exact resolve eq198755 eq6715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6715 eq198755
  have eq198972 : ∀ X0 : G, (M.op (M.op x y) X0) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq794 eq198763
    | exact resolve eq198763 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq198983 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq198763 eq74383
    | exact resolve eq74383 eq198763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198999 : ∀ X0 : G, (k (M.op (σ x) (M.op (σ x) (σ y))) (σ X0)) = (σ (k (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq198763 eq10
    | exact resolve eq10 eq198763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199713 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (σ (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq198761 eq74383
    | exact resolve eq74383 eq198761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74383
  have eq199732 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq198761 eq15
    | exact resolve eq15 eq198761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199800 : ∀ X0 X1 : G, (k (M.op (σ x) (M.op (σ x) (σ y))) (τ X1)) = (τ (k (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq198761 eq6753
    | exact resolve eq6753 eq198761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753 eq198761
  have eq200749 : ∀ X0 : G, (M.op (M.op x y) X0) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq198972 eq15
    | exact resolve eq15 eq198972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198972
  have eq201401 : ∀ X0 X1 : G, (σ (k (M.op (M.op x y) X0) X1)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq198983 eq10
    | exact resolve eq10 eq198983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202146 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (σ (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq150691 eq199713
    | exact resolve eq199713 eq150691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150691
  have eq202610 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (τ (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq199713 eq15
    | exact resolve eq15 eq199713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203116 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq198999 eq202146
    | exact resolve eq202146 eq198999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198999 eq202146
  have eq254526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq37467 eq1261
    | exact resolve eq1261 eq37467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261 eq37467
  have eq254535 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq254526
       have r₂ := eq27
       grind)
    | exact resolve eq254526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254526
  have eq254557 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq254535 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq254535
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq254535
       grind)
    | exact resolve eq13 eq254535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254535
  have eq254600 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq254557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254557
  have eq254774 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq254600 eq107
    | exact resolve eq107 eq254600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq254600
  have eq254782 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq254774
    | exact resolve eq254774 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254774
  have eq254839 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq1282 y
       grind)
    | (have r₁ := eq254782
       have r₂ := eq1282 y
       grind)
    | exact resolve eq254782 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq254782
  have eq254875 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq254839 eq538
    | exact resolve eq538 eq254839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254914 : ∀ X0 : G, (σ x) = (M.op (M.op x y) X0) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq254839 eq254875
    | exact resolve eq254875 eq254839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254839 eq254875
  have eq255317 : (σ x) = (τ (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq254914 eq200749
    | exact resolve eq200749 eq254914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255671 : y = (M.op y y) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq255317
    | exact resolve eq255317 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq255317
  have eq256557 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq255671
       grind)
    | exact superpose eq255671 eq13
    | (have r₁ := eq13 X0 y
       have r₂ := eq255671
       grind)
    | exact resolve eq13 eq255671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256593 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (M.op x y) X0) y) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq150636 X0 y y
       have i₂ := eq255671
       grind)
    | exact superpose eq255671 eq150636
    | exact resolve eq150636 eq255671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150636 eq255671
  have eq256602 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq256557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256557
  have eq256699 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq8128 y
       have i₂ := eq256602 y
       grind)
    | exact superpose eq256602 eq8128
    | (have j0 := eq8128 y
       grind)
    | exact resolve eq8128 eq256602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8128
  have eq256735 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq256602 (τ X0)
       grind)
    | exact superpose eq256602 eq34
    | exact resolve eq34 eq256602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256786 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (σ x) := by grind
  clear eq256699
  have eq256815 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq256735 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq256735
    | (have j0 := eq256735 X0
       grind)
    | exact resolve eq256735 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256735
  have eq256827 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq256786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq256786
    | exact resolve eq256786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256786
  have eq256964 : ∀ X0 : G, (σ (σ y)) = (k X0 (σ (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq256815 eq34
    | exact resolve eq34 eq256815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq256815
  have eq257139 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq256827 eq203116
    | exact resolve eq203116 eq256827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203116 eq256827
  have eq257144 : ∀ X0 : G, (M.op (M.op x y) X0) = (σ (σ y)) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq256964 eq257139
    | exact resolve eq257139 eq256964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256964 eq257139
  have eq258102 : ∀ X0 : G, (k (M.op (M.op x y) X0) y) = (k (σ (σ y)) y) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq257144 eq74420
    | exact resolve eq74420 eq257144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74420
  have eq258215 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (σ (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq257144 eq199732
    | exact resolve eq199732 eq257144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199732
  have eq258225 : ∀ X0 : G, (M.op (M.op x y) X0) = (τ (σ (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq257144 eq202610
    | exact resolve eq202610 eq257144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257144
  have eq258592 : ∀ X0 : G, (σ y) = (M.op (M.op x y) X0) ∨ x = (M.op y x) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq258225 X0
       have i₂ := eq15 sF3
       grind)
    | exact superpose eq15 eq258225
    | exact resolve eq258225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258225
  have eq258602 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq258215
       have i₂ := eq15 sF3
       grind)
    | exact superpose eq15 eq258215
    | exact resolve eq258215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258215
  have eq258704 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (σ y)) y) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq256593 eq258102
    | exact resolve eq258102 eq256593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256593 eq258102
  have eq259105 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq256602 eq258704
    | exact resolve eq258704 eq256602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256602 eq258704
  have eq259387 : x = (M.op y x) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq258602 eq259105
    | exact resolve eq259105 eq258602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259105
  have eq259631 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y x) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq954 y x
       have i₂ := eq259387
       grind)
    | exact superpose eq259387 eq954
    | exact resolve eq954 eq259387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259659 : x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq259387 eq259631
    | exact resolve eq259631 eq259387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259387 eq259631
  have eq259800 : x = (σ x) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq259659 eq198763
    | exact resolve eq198763 eq259659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259659
  have eq259942 : x = (σ x) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq259800
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq259800
    | exact resolve eq259800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259800
  have eq259943 : y = (σ y) ∨ x = (σ x) := by grind
  clear eq259942
  have eq260032 : (M.op x y) = (M.op x (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq259943
       grind)
    | exact superpose eq259943 eq18
    | exact resolve eq18 eq259943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260033 : (σ y) = (σ (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq259943
       grind)
    | exact superpose eq259943 eq24
    | exact resolve eq24 eq259943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264866 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq258592 eq1947
    | exact resolve eq1947 eq258592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947 eq258592
  have eq265525 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq26 eq264866
    | exact resolve eq264866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264866
  have eq265911 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (σ x) := by
    first
    | exact superpose eq258602 eq265525
    | exact resolve eq265525 eq258602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258602 eq265525
  have eq266149 : x = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq259943 eq265911
    | exact resolve eq265911 eq259943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259943 eq265911
  have eq266368 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq266149 eq954
    | exact resolve eq954 eq266149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq266396 : x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq266149 eq266368
    | exact resolve eq266368 eq266149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266149 eq266368
  have eq266522 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq266396 eq198763
    | exact resolve eq198763 eq266396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266396
  have eq266664 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq266522
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq266522
    | exact resolve eq266522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq266522
  have eq266665 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq266664
  have eq266841 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq266665 eq1967
    | exact resolve eq1967 eq266665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq267045 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq26 eq266841
    | (have j0 := eq266841 X0
       grind)
    | exact resolve eq266841 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266841
  have eq267198 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq266665 eq267045
    | exact resolve eq267045 eq266665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267045
  have eq267987 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq267198 eq260032
    | exact resolve eq260032 eq267198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268042 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq267198 eq1948
    | exact resolve eq1948 eq267198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq267198
  have eq268209 : (M.op x y) = (σ y) ∨ x = (σ x) := by grind
  clear eq267987
  have eq268347 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq260032 eq268042
    | exact resolve eq268042 eq260032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260032 eq268042
  have eq268754 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq266665 eq268347
    | exact resolve eq268347 eq266665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266665 eq268347
  have eq269114 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq26 eq268754
    | exact resolve eq268754 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268754
  have eq269853 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq268209 eq260033
    | exact resolve eq260033 eq268209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260033 eq268209
  have eq269868 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq269853
  have eq269877 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq269868
    | exact resolve eq269868 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269868
  have eq270103 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq269114 eq27
    | exact resolve eq27 eq269114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269114
  have eq270419 : x = (σ x) := by
    first
    | (have r₁ := eq270103
       have r₂ := eq269877
       grind)
    | exact resolve eq270103 eq269877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269877 eq270103
  have eq270516 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq270419
       grind)
    | exact superpose eq270419 eq18
    | exact resolve eq18 eq270419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq270520 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq781 X0
       have i₂ := eq270419
       grind)
    | exact superpose eq270419 eq781
    | exact resolve eq781 eq270419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq270522 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq956
       have i₂ := eq270419
       grind)
    | exact superpose eq270419 eq956
    | exact resolve eq956 eq270419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq270525 : (M.op x y) = (k (σ x) y) ∨ (σ x) = (M.op y (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1238
       have i₂ := eq270419
       grind)
    | exact superpose eq270419 eq1238
    | exact resolve eq1238 eq270419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq271252 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq270516 eq766
    | exact resolve eq766 eq270516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq271605 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (σ x) (M.op x y)) := by
    intro X1 X2 X3
    first
    | exact superpose eq270520 eq853
    | exact resolve eq853 eq270520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq271673 : ∀ X0 X1 : G, (σ (k (M.op (M.op x y) X0) X1)) = (σ (k (M.op (σ x) (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq270520 eq74427
    | exact resolve eq74427 eq270520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74427
  have eq271779 : ∀ X0 : G, (M.op (M.op x y) X0) = (σ (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq270520 eq199713
    | exact resolve eq199713 eq270520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199713
  have eq271833 : (σ x) = (M.op (σ x) (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq270520 eq254914
    | exact resolve eq254914 eq270520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272060 : (σ x) = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq271833
       have i₂ := eq270419
       grind)
    | exact superpose eq270419 eq271833
    | exact resolve eq271833 eq270419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271833
  have eq272172 : ∀ X1 : G, (k (M.op (σ x) (M.op (σ x) (σ y))) (σ X1)) = (σ (k (M.op (σ x) (M.op x y)) X1)) := by
    intro X1
    first
    | exact superpose eq201401 eq271673
    | exact resolve eq271673 eq201401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201401 eq271673
  have eq272385 : ∀ X1 : G, (σ (k (M.op (σ x) (M.op x y)) X1)) = (k (M.op (σ x) (M.op x y)) (σ X1)) := by
    intro X1
    first
    | exact superpose eq270522 eq272172
    | exact resolve eq272172 eq270522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272172
  have eq272705 : ∀ X0 X1 : G, (σ (k (M.op (M.op x y) X0) X1)) = (σ (k (M.op (σ x) (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq270522 eq74126
    | exact resolve eq74126 eq270522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74126
  have eq272874 : ∀ X0 X1 : G, (σ (k (M.op (M.op x y) X0) X1)) = (k (M.op (σ x) (M.op x y)) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq272385 eq272705
    | exact resolve eq272705 eq272385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272385 eq272705
  have eq395716 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1533 eq272874
    | exact resolve eq272874 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq272874
  have eq396046 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq395716
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq395716
    | exact resolve eq395716 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395716
  have eq396342 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq198763 eq396046
    | exact resolve eq396046 eq198763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198763 eq396046
  have eq396560 : (M.op (σ x) (M.op x y)) = (k (M.op (σ x) (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq270522 eq396342
    | exact resolve eq396342 eq270522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396342
  have eq481924 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq270520 eq396560
    | exact resolve eq396560 eq270520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270520 eq396560
  have eq497793 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X1) (σ y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq481924 eq150507
    | exact resolve eq150507 eq481924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150507 eq481924
  have eq543380 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (τ (k (M.op (M.op x y) X0) (σ y))) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq497793 eq202610
    | exact resolve eq202610 eq497793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497793
  have eq544082 : ∀ X1 : G, (M.op (M.op x y) X1) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (σ y))) ∨ y = (M.op y y) := by
    intro X1
    first
    | exact superpose eq199800 eq543380
    | exact resolve eq543380 eq199800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199800 eq543380
  have eq544800 : ∀ X1 : G, (M.op (M.op x y) X1) = (k (M.op (σ x) (M.op (σ x) (σ y))) y) ∨ y = (M.op y y) := by
    intro X1
    first
    | exact superpose eq31 eq544082
    | exact resolve eq544082 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544082
  have eq545311 : ∀ X1 : G, (M.op (M.op x y) X1) = (k (M.op (σ x) (M.op x y)) y) ∨ y = (M.op y y) := by
    intro X1
    first
    | exact superpose eq270522 eq544800
    | exact resolve eq544800 eq270522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544800
  have eq603448 : (σ x) = (k (M.op (σ x) (M.op x y)) y) ∨ x = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq545311 eq254914
    | exact resolve eq254914 eq545311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254914 eq545311
  have eq603835 : (σ x) = (k (M.op (σ x) (M.op x y)) y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq603448
  have eq604108 : (σ x) = (M.op y (σ x)) ∨ (σ x) = (k (M.op (σ x) (M.op x y)) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq603835
       have i₂ := eq270419
       grind)
    | exact superpose eq270419 eq603835
    | exact resolve eq603835 eq270419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270419 eq603835
  have eq604703 : (σ x) = (M.op y (σ x)) ∨ (σ x) = (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq272060 eq604108
    | exact resolve eq604108 eq272060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272060 eq604108
  have eq605138 : (σ x) = (M.op y (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq270525 eq604703
    | exact resolve eq604703 eq270525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270525 eq604703
  have eq605806 : (M.op y (σ x)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq605138 eq271252
    | exact resolve eq271252 eq605138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605869 : (σ x) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq605138 eq605806
    | exact resolve eq605806 eq605138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605138 eq605806
  have eq606243 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq605869 eq271605
    | exact resolve eq271605 eq605869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271605 eq605869
  have eq611995 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq606243 eq270516
    | exact resolve eq270516 eq606243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606243
  have eq612461 : y = (M.op y y) ∨ (M.op x y) = (σ x) := by grind
  clear eq611995
  have eq612764 : y ≠ (k y y) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq149082 y
       have i₂ := eq612461
       grind)
    | exact superpose eq612461 eq149082
    | (have j0 := eq149082 y
       grind)
    | exact resolve eq149082 eq612461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149082
  have eq612765 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq612461
       grind)
    | exact superpose eq612461 eq13
    | (have r₁ := eq13 X0 y
       have r₂ := eq612461
       grind)
    | exact resolve eq13 eq612461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612461
  have eq612862 : ∀ X0 : G, y = (k X0 y) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | (have j0 := eq612765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612765
  have eq612863 : y ≠ (k y y) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) := by grind
  clear eq612764
  have eq612915 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq612863
       have r₂ := eq612862 y
       grind)
    | exact resolve eq612863 eq612862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612862 eq612863
  have eq612957 : y = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq270522 eq612915
    | exact resolve eq612915 eq270522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270522 eq612915
  have eq613295 : ∀ X0 : G, (σ y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | exact superpose eq612957 eq271779
    | exact resolve eq271779 eq612957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271779
  have eq613406 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) y) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | exact superpose eq612957 eq538
    | exact resolve eq538 eq612957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq613454 : y = (M.op (σ x) y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq612957 eq271252
    | exact resolve eq271252 eq612957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271252
  have eq613504 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq270516 eq613454
    | exact resolve eq613454 eq270516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613454
  have eq613528 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | exact superpose eq270516 eq613406
    | exact resolve eq613406 eq270516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613406
  have eq613555 : ∀ X0 : G, (σ y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq613295 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq613295
    | (have j0 := eq613295 X0
       grind)
    | exact resolve eq613295 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq613295
  have eq613603 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq613528 eq613555
    | exact resolve eq613555 eq613528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613528 eq613555
  have eq614257 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq613603 eq26
    | exact resolve eq26 eq613603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614258 : y = (τ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq613603 eq31
    | exact resolve eq31 eq613603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq613603
  have eq614472 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq613504 eq614258
    | exact resolve eq614258 eq613504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614258
  have eq614473 : y = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq612957 eq614257
    | exact resolve eq614257 eq612957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612957 eq614257
  have eq614519 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq613504 eq614473
    | exact resolve eq614473 eq613504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613504 eq614473
  have eq614845 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq614519 eq27
    | exact resolve eq27 eq614519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614519
  have eq615623 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq614472 eq14
    | exact resolve eq14 eq614472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614472
  have eq615708 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq20 eq615623
    | exact resolve eq615623 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615623
  have eq615731 : (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq615708
       have r₂ := eq614845
       grind)
    | exact resolve eq615708 eq614845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614845 eq615708
  have eq615742 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq615731 eq26
    | exact resolve eq26 eq615731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq615923 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq615731 eq270516
    | exact resolve eq270516 eq615731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270516 eq615731
  have eq625013 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq615742 eq770
    | exact resolve eq770 eq615742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq625122 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq615742 eq200749
    | exact resolve eq200749 eq615742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200749
  have eq625127 : ∀ X0 : G, (M.op (M.op x y) X0) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq615742 eq202610
    | exact resolve eq202610 eq615742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202610 eq615742
  have eq625531 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (τ (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq625127 eq625013
    | exact resolve eq625013 eq625127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625013 eq625127
  have eq625702 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq625122 eq625531
    | exact resolve eq625531 eq625122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625122 eq625531
  have eq626780 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq615923 eq198983
    | exact resolve eq198983 eq615923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198983 eq615923
  have eq627137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq625702 eq626780
    | exact resolve eq626780 eq625702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625702 eq626780
  have eq627344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq627137
    | exact resolve eq627137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq627137
  have eq627523 : False := by grind
  exact eq627523

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq49
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq51 X1 X0
       grind)
    | (have r₁ := eq102 X1 X0
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq102 X0 X0
       have r₂ := eq51 X0 X0
       grind)
    | exact resolve eq102 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq102
  have eq254 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq106 (σ X1) (σ X0)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq106 X1 X0
       grind)
    | exact superpose eq106 eq254
    | exact resolve eq254 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq254
  have eq263 : False := by grind
  exact eq263

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyy_pxx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  clear eq25 eq36
  have eq48 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 X0
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67
    | exact resolve eq67 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq70
    | exact resolve eq70 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq71
    | exact resolve eq71 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq81 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq371 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq44
    | (have j1 := eq83 x
       grind)
    | exact resolve eq44 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq83
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op X0 (M.op X0 (σ y))) (M.op X2 (M.op X2 (M.op X1 (M.op X1 (M.op (σ x) (σ y))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq680 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X0 (M.op X3 X0))))) = (M.op (M.op X1 (M.op X1 (M.op X2 (M.op X0 (M.op X3 X0))))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (M.op X0 (M.op X3 X0)) X1 X2 X0
       have i₂ := eq14 X0 X0 X3
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq4544 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op X0 (M.op X0 (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq652 X0 sF4 sF4
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq652
    | exact resolve eq652 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq6320 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq173 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq173
    | (have j0 := eq173 x
       grind)
    | exact resolve eq173 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq6352 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq6320
    | exact resolve eq6320 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320
  have eq6368 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6352
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq6352
    | exact resolve eq6352 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6352
  have eq6373 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq6368
    | exact resolve eq6368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368
  have eq12332 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (M.op X0 (M.op X0 (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq4544 eq14
    | exact resolve eq14 eq4544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15059 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq12332 eq680
    | exact resolve eq680 eq12332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq12332
  have eq18109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq72 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18109
    | exact resolve eq18109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18109
  have eq18121 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18110
       have r₂ := eq28
       grind)
    | exact resolve eq18110 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18110
  have eq18123 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18121
    | exact resolve eq18121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121
  have eq18126 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18123 eq81
    | (have r₁ := eq81
       have r₂ := eq18123
       grind)
    | exact resolve eq81 eq18123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18169 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18126
  have eq18170 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18169
  have eq18452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18170 eq72
    | exact resolve eq72 eq18170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18170
  have eq18461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq18452
  have eq18464 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq18461
       have r₂ := eq28
       grind)
    | exact resolve eq18461 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18461
  have eq18479 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  have eq18492 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18464 eq51
    | exact resolve eq51 eq18464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18464
  have eq18520 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18492
    | exact resolve eq18492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18492
  have eq18770 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq371
       have i₂ := eq18520
       grind)
    | exact superpose eq18520 eq371
    | exact resolve eq371 eq18520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18771 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18520
       grind)
    | exact superpose eq18520 eq80
    | (have r₁ := eq80
       have r₂ := eq18520
       grind)
    | exact resolve eq80 eq18520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq18814 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18771
  have eq18815 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18814
  have eq18816 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18770
    | exact resolve eq18770 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18770
  have eq19115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq18815
       grind)
    | exact superpose eq18815 eq45
    | exact resolve eq45 eq18815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18815
  have eq19135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19115
    | exact resolve eq19115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115
  have eq19168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19135 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq19135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19168
    | exact resolve eq19168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19168
  have eq19182 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19171
       have r₂ := eq28
       grind)
    | exact resolve eq19171 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19171
  have eq19184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq19182
    | exact resolve eq19182 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19182
  have eq19193 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18479 eq72
    | exact resolve eq72 eq18479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq18479
  have eq19205 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq19193
  have eq19218 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq371
       have i₂ := eq19205
       grind)
    | exact superpose eq19205 eq371
    | exact resolve eq371 eq19205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq19219 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19205
       grind)
    | exact superpose eq19205 eq80
    | (have r₁ := eq80
       have r₂ := eq19205
       grind)
    | exact resolve eq80 eq19205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq19205
  have eq19262 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq19219
  have eq19263 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq19262
  have eq19264 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq19218
    | exact resolve eq19218 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19218
  have eq19568 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19263
       grind)
    | exact superpose eq19263 eq45
    | exact resolve eq45 eq19263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19263
  have eq19588 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq19568
    | exact resolve eq19568 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19568
  have eq19623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19588 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq19588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19628 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq19623
    | exact resolve eq19623 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19623
  have eq19639 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq19628
       have r₂ := eq28
       grind)
    | exact resolve eq19628 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19628
  have eq19641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq19639
    | exact resolve eq19639 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19639
  have eq23693 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19184 eq81
    | (have r₁ := eq81
       have r₂ := eq19184
       grind)
    | exact resolve eq81 eq19184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23703 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19184 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19184
       grind)
    | exact resolve eq12 eq19184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19184
  have eq23737 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq23703
  have eq23738 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq23737
  have eq23739 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23693
  have eq23740 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23739
  have eq24026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23738 eq18816
    | exact resolve eq18816 eq23738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18816 eq23738
  have eq24035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq24026
  have eq24041 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24035
       have r₂ := eq28
       grind)
    | exact resolve eq24035 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24035
  have eq24071 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24041 eq51
    | exact resolve eq51 eq24041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24041
  have eq24101 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq24071
    | exact resolve eq24071 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24071
  have eq24102 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24101
  have eq24182 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq24102
       grind)
    | exact superpose eq24102 eq51
    | exact resolve eq51 eq24102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24102
  have eq24212 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24182
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24182
    | exact resolve eq24182 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24182
  have eq24213 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24212
  have eq24215 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24213 eq28
    | exact resolve eq28 eq24213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24213
  have eq30869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23740 eq19135
    | exact resolve eq19135 eq23740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19135 eq23740
  have eq30890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq30869
  have eq30909 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30890
       have r₂ := eq28
       grind)
    | exact resolve eq30890 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30890
  have eq31193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30909 eq51
    | exact resolve eq51 eq30909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30909
  have eq31225 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq31193
    | exact resolve eq31193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31193
  have eq31226 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31225
  have eq31242 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31226
  have eq31294 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq31242
       grind)
    | exact superpose eq31242 eq45
    | exact resolve eq45 eq31242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq31242
  have eq31335 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31294
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31294
    | exact resolve eq31294 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31294
  have eq31602 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31335 eq6373
    | exact resolve eq6373 eq31335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6373
  have eq31632 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq31602
  have eq34817 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq31632 eq81
    | (have r₁ := eq81
       have r₂ := eq31632
       grind)
    | exact resolve eq81 eq31632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq31632
  have eq34876 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34817
  have eq34877 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34876
  have eq35476 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34877 eq31335
    | exact resolve eq31335 eq34877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31335 eq34877
  have eq35479 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35476
  have eq35530 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35479 eq51
    | exact resolve eq51 eq35479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35479
  have eq35562 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35530
    | exact resolve eq35530 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq35530
  have eq35563 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35562
  have eq35818 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq35563 eq28
    | exact resolve eq28 eq35563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq35832 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op X0 (M.op X0 (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq35563 eq4544
    | exact resolve eq4544 eq35563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4544
  have eq35836 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq35563 eq15059
    | exact resolve eq15059 eq35563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15059
  have eq36722 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq19641 eq35836
    | exact resolve eq35836 eq19641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19641 eq35836
  have eq36819 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq36722 X0
       grind)
    | (have r₁ := eq36722 X0
       have r₂ := eq35818
       grind)
    | exact resolve eq36722 eq35818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36722
  have eq36820 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq35563 eq36819
    | exact resolve eq36819 eq35563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35563 eq36819
  have eq54778 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq36820 eq35832
    | exact resolve eq35832 eq36820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35832 eq36820
  have eq54898 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq54778
  have eq55234 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq54898 eq19588
    | exact resolve eq19588 eq54898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19588 eq54898
  have eq55245 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq55234
  have eq55271 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq55245
       have r₂ := eq35818
       grind)
    | exact resolve eq55245 eq35818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55245
  have eq55322 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq55271
  have eq55396 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq55322 eq19264
    | exact resolve eq19264 eq55322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19264 eq55322
  have eq55415 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq55396
  have eq55424 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq55415
       have r₂ := eq24215
       grind)
    | exact resolve eq55415 eq24215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24215 eq55415
  have eq55463 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq55424
       grind)
    | exact superpose eq55424 eq51
    | exact resolve eq51 eq55424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq55424
  have eq55495 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55463
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55463
    | exact resolve eq55463 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq55463
  have eq55496 : x = (M.op x y) := by grind
  clear eq55495
  have eq55498 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq55496 eq21
    | exact resolve eq21 eq55496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq55496
  have eq55786 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq55498
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq55498
    | exact resolve eq55498 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq55498
  have eq55787 : False := by grind
  exact eq55787

/-- `Equation4439`: `x ◇ (y ◇ x) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxx_x_pyx_Equation4439 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4439 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4439.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X1) := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X0) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X0) X0 X3
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X2 X3
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq55 X0 x X2 X3
       have i₂ := eq14 X0 X3 (M.op x X0)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X2 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 X0) X0
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X2 X0) X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X1 ∨ (k X1 (M.op X0 X2)) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op X0 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq85 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq102 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq103 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq107 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq110
  have eq118 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq107
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq219 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op x (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X1)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X1 (M.op X0 x)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op x y) (M.op X1 (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq222 x X1
       have i₂ := eq14 sF0 X1 x
       grind)
    | exact superpose eq14 eq222
    | exact resolve eq222 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq225 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (M.op X1 (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq224 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq224
    | exact resolve eq224 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq229 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X1 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq229 x X1
       have i₂ := eq14 sF4 X1 x
       grind)
    | exact superpose eq14 eq229
    | exact resolve eq229 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq232 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq57 eq231
    | exact resolve eq231 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq467 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X0 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 (M.op X2 X0) X3 X4
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op X0 X1) x)) = (M.op (M.op x y) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X0 X2)
       have i₂ := eq52 X0 X2 x X1
       grind)
    | (have i₁ := eq56 (M.op X0 X2)
       have i₂ := eq52 X0 X1 x X2
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op X0 X1) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op X0 X1)
       have i₂ := eq52 X0 X1 sF2 x
       grind)
    | (have i₁ := eq57 (M.op X0 x)
       have i₂ := eq52 X0 X1 sF2 x
       grind)
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq516 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq513
    | exact resolve eq513 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq518 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq511 X0 X1 X2
       have i₂ := eq56 (M.op X0 X1)
       grind)
    | exact superpose eq56 eq511
    | exact resolve eq511 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq766 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq516
    | (have j0 := eq516 (σ x) X0 (σ y)
       grind)
    | exact resolve eq516 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq232 eq516
    | exact resolve eq516 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq849 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq232 eq766
    | exact resolve eq766 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (M.op X1 (σ x)))) = (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 X0 X2 x
       have i₂ := eq14 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op X0 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 x X0 X2 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X0 X1) (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq920
    | exact resolve eq920 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1192 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 X0 X0
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1200 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op (M.op X0 x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0 x x
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 x X1
       have i₂ := eq51 X1 X0 (M.op X0 x) x
       grind)
    | exact superpose eq51 eq59
    | exact resolve eq59 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1202 x
       have i₂ := eq51 sF4 x x sF2
       grind)
    | exact superpose eq51 eq1202
    | exact resolve eq1202 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1260 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 (M.op (M.op x y) (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1200 x
       have i₂ := eq51 sF0 x x x
       grind)
    | exact superpose eq51 eq1200
    | exact resolve eq1200 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1287 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq232 eq1258
    | exact resolve eq1258 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1288 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq225 eq1260
    | exact resolve eq1260 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1333 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 x X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq70
    | (have j0 := eq70 x X0 X1
       grind)
    | exact resolve eq70 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1335 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq70
    | (have j0 := eq70 (σ x) X0 X1
       grind)
    | exact resolve eq70 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1488 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X2)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op (M.op X2 sF2) x)
       have i₂ := eq50 sF2 X1 X2 x
       grind)
    | exact superpose eq50 eq57
    | exact resolve eq57 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : ∀ X0 X2 : G, (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op X0 (σ x))))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1488 x X2 X2
       have i₂ := eq14 sF2 x X2
       grind)
    | exact superpose eq14 eq1488
    | exact resolve eq1488 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1572 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op X0 (σ x))))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq771 eq1520
    | exact resolve eq1520 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq1609 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op X0 (σ x))))) := by
    intro X0
    first
    | exact superpose eq771 eq1572
    | exact resolve eq1572 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1632 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (M.op X0 (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq1609 x
       have i₂ := eq51 sF2 x (M.op x sF2) sF2
       grind)
    | exact superpose eq51 eq1609
    | exact resolve eq1609 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1609
  have eq1648 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq57 eq1632
    | exact resolve eq1632 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq2118 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq518 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq518
    | (have j0 := eq518 x y X0
       grind)
    | exact resolve eq518 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2135 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq225 eq518
    | exact resolve eq518 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq2290 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq225 eq2118
    | exact resolve eq2118 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2488 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op (M.op X1 X2) X0)) ∨ (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 X1) x X1
       have i₂ := eq50 X1 X2 X0 x
       grind)
    | exact superpose eq50 eq69
    | (have j0 := eq69 (M.op X0 X1) X1 X1
       grind)
    | (have r₁ := eq69 X1 X1 (M.op (M.op X1 X1) X1)
       have r₂ := eq50 X1 X1 X1 X1
       grind)
    | exact resolve eq69 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq69
  have eq2502 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = (M.op X1 (M.op (M.op X1 (M.op X0 X1)) X1)) ∨ (M.op X1 (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2488 X0 X1 X2
       have i₂ := eq14 X1 (M.op X1 (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq2488
    | (have j0 := eq2488 X0 X1 X2
       grind)
    | exact resolve eq2488 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2512 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = (M.op X1 (M.op X1 (M.op X1 X1))) ∨ (M.op X1 (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2502 X0 X1 X2
       have i₂ := eq14 X1 X1 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq2502
    | (have j0 := eq2502 X0 X1 X2
       grind)
    | exact resolve eq2502 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2952 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq101 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq101 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq101 X0 X1
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2953 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq101 X0 X1
       grind)
    | exact resolve eq13 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2977 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq101 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2978 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq101 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq2979 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2977 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977
  have eq2980 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2952 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq2985 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2953 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2953 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2953 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq2953 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953
  have eq2986 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2980 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2980 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2980 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq2980 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq2995 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2985 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq2985
    | (have j0 := eq2985 X0 X1
       grind)
    | exact resolve eq2985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985
  have eq2996 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2986 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq2986
    | (have j0 := eq2986 X0 X1
       grind)
    | exact resolve eq2986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3016 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1287 X0
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq1287
    | exact resolve eq1287 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3286 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x X0)) = (M.op (M.op (M.op X0 X1) X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1288 X0
       have i₂ := eq54 X0 X1 X2 sF0
       grind)
    | exact superpose eq54 eq1288
    | exact resolve eq1288 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3562 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op X0 (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq1287 eq1648
    | exact resolve eq1648 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq3564 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq3562
    | (have j0 := eq3562 (σ y)
       grind)
    | exact resolve eq3562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3876 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op X0 (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq2135 eq219
    | exact resolve eq219 eq2135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq4645 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3016 X0 X1
       have i₂ := eq14 X0 sF2 X2
       grind)
    | exact superpose eq14 eq3016
    | exact resolve eq3016 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4707 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (M.op X0 X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq3016 eq3562
    | exact resolve eq3562 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6706 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x X0)) = (M.op (M.op X0 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1288 eq958
    | exact resolve eq958 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq6754 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op X0 X1) (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1287 eq960
    | exact resolve eq960 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq6804 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) X1)) = (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1287 eq1047
    | exact resolve eq1047 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq7867 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op x (M.op (M.op X0 X1) (M.op x X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3876 X0
       have i₂ := eq6706 X0 X1 X2
       grind)
    | exact superpose eq6706 eq3876
    | exact resolve eq3876 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876 eq6706
  have eq11421 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x (M.op x y))) ∨ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1288 eq1333
    | (have j0 := eq1333 (M.op (M.op x y) (M.op x y)) X0
       grind)
    | exact resolve eq1333 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq1333
  have eq11424 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq11421 X0
       grind)
    | (have r₁ := eq11421 X0
       have r₂ := eq2118 (M.op x y)
       grind)
    | exact resolve eq11421 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118 eq11421
  have eq11436 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq2290 eq11424
    | exact resolve eq11424 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11424
  have eq11445 : ∀ X0 : G, (k (M.op (M.op x y) x) (M.op x X0)) = (M.op (M.op x y) (M.op (M.op (M.op x y) x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq11436 X0
       have i₂ := eq14 sF0 (M.op sF0 x) x
       grind)
    | exact superpose eq14 eq11436
    | exact resolve eq11436 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11436
  have eq11453 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq225 eq11445
    | exact resolve eq11445 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq11445
  have eq11461 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq2135 eq11453
    | exact resolve eq11453 eq2135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135 eq11453
  have eq11467 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq2290 eq11461
    | exact resolve eq11461 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11461
  have eq11473 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq11467 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11467
    | (have j0 := eq11467 y
       grind)
    | exact resolve eq11467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11540 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1287 eq1335
    | (have j0 := eq1335 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq1335 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq11541 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq11540 X0
       grind)
    | (have r₁ := eq11540 X0
       have r₂ := eq766 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11540 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11540
  have eq11551 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq849 eq11541
    | exact resolve eq11541 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11541
  have eq11558 : ∀ X0 : G, (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq11551 X0
       have i₂ := eq14 sF4 (M.op sF4 sF2) sF2
       grind)
    | exact superpose eq14 eq11551
    | exact resolve eq11551 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11551
  have eq11564 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq232 eq11558
    | exact resolve eq11558 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq11558
  have eq11570 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq771 eq11564
    | exact resolve eq11564 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq11564
  have eq11574 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq849 eq11570
    | exact resolve eq11570 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11570
  have eq11581 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq11574
    | (have j0 := eq11574 (σ y)
       grind)
    | exact resolve eq11574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11574
  have eq17314 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq930 X0 X1 X2
       have i₂ := eq1209 X0 X1
       grind)
    | exact superpose eq1209 eq930
    | exact resolve eq930 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq19967 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq19998 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq95 eq19967
    | exact resolve eq19967 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq19967
  have eq20001 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq19998
       have r₂ := eq13 y y
       grind)
    | exact resolve eq19998 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19998
  have eq20002 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq20001
       grind)
    | exact superpose eq20001 eq80
    | exact resolve eq80 eq20001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20001
  have eq20301 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq16
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq20334 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq20301
    | exact resolve eq20301 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq20301
  have eq20337 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq20334
       have r₂ := eq13 x x
       grind)
    | exact resolve eq20334 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20334
  have eq20338 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq20337
       grind)
    | exact superpose eq20337 eq43
    | exact resolve eq43 eq20337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq22076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22075
    | exact resolve eq22075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22075
  have eq22087 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq22076
       have r₂ := eq27
       grind)
    | exact resolve eq22076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22076
  have eq22089 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22087
    | exact resolve eq22087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22087
  have eq22092 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22089 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22089
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22089
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22089
       grind)
    | exact resolve eq12 eq22089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22089
  have eq22145 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq22092
  have eq22179 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22145
    | exact resolve eq22145 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22145
  have eq22180 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq22179
  have eq22210 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22180 eq90
    | exact resolve eq90 eq22180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq22180
  have eq22229 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq22210
    | exact resolve eq22210 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22210
  have eq22520 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq22229
       grind)
    | exact superpose eq22229 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq22229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22229
  have eq22521 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22520
  have eq22523 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22521
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22521
    | exact resolve eq22521 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22521
  have eq22524 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22523
  have eq22534 : (M.op x x) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq22524
       grind)
    | exact superpose eq22524 eq56
    | exact resolve eq56 eq22524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22535 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq22524
       grind)
    | exact superpose eq22524 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq22524
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22524
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22524
       grind)
    | exact resolve eq12 eq22524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22536 : x ≠ x ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq22524
       grind)
    | exact superpose eq22524 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22524
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22524
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22524
       grind)
    | exact resolve eq13 eq22524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22537 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq22524
       grind)
    | exact superpose eq22524 eq14
    | exact resolve eq14 eq22524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22546 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq59 y x x
       have i₂ := eq22524
       grind)
    | exact superpose eq22524 eq59
    | exact resolve eq59 eq22524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22524
  have eq22587 : (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22536
  have eq22588 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22535
  have eq22613 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22546 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq22546
    | exact resolve eq22546 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22546
  have eq22622 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22588
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22588
    | exact resolve eq22588 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22588
  have eq22623 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22622
  have eq22650 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq22623
       grind)
    | exact superpose eq22623 eq79
    | exact resolve eq79 eq22623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22666 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22650
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22650
    | exact resolve eq22650 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22650
  have eq22680 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22666 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq22666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22666
  have eq22681 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22680
  have eq22685 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22681
    | exact resolve eq22681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22681
  have eq22686 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22685
  have eq22700 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22686 eq57
    | exact resolve eq57 eq22686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22702 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22686 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22686
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22686
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22686
       grind)
    | exact resolve eq13 eq22686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22703 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22686 eq14
    | exact resolve eq14 eq22686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22712 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22686 eq59
    | exact resolve eq59 eq22686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq22686
  have eq22753 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22702
  have eq22779 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq57 eq22712
    | exact resolve eq22712 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22712
  have eq23127 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq22587
       grind)
    | exact superpose eq22587 eq44
    | exact resolve eq44 eq22587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22587
  have eq23141 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23127
       have i₂ := eq20338
       grind)
    | exact superpose eq20338 eq23127
    | exact resolve eq23127 eq20338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23127
  have eq24360 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22753 eq23141
    | exact resolve eq23141 eq22753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22753 eq23141
  have eq24362 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24360
  have eq27591 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22537 X0
       have i₂ := eq22613 X0
       grind)
    | exact superpose eq22613 eq22537
    | exact resolve eq22537 eq22613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22537 eq22613
  have eq27666 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq27591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27591
  have eq27960 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27666 eq22534
    | exact resolve eq22534 eq27666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22534 eq27666
  have eq28050 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27960
  have eq28127 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28050
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28050
    | exact resolve eq28050 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28050
  have eq28245 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20338
       have i₂ := eq28127
       grind)
    | exact superpose eq28127 eq20338
    | exact resolve eq20338 eq28127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28127
  have eq28350 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq28245
    | exact resolve eq28245 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28245
  have eq28649 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28350 eq24362
    | exact resolve eq24362 eq28350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24362 eq28350
  have eq28652 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28649
  have eq57884 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq102 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102
    | (have j0 := eq102 x
       grind)
    | exact resolve eq102 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq57956 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq57884
  have eq57975 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57956
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq57956
    | exact resolve eq57956 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq57956
  have eq58012 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq57975
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq57975 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57975
  have eq58131 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq103
    | (have j0 := eq103 y
       grind)
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq58199 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq58131
  have eq58215 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq58199
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq58199
    | exact resolve eq58199 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq58199
  have eq58250 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq58215
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq58215 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58215
  have eq60510 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2996 y x
       have i₂ := eq22623
       grind)
    | exact superpose eq22623 eq2996
    | (have j0 := eq2996 y x
       grind)
    | exact resolve eq2996 eq22623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996 eq22623
  have eq60702 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60510
  have eq60854 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60702
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq60702
    | exact resolve eq60702 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq60702
  have eq61005 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60854
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60854
    | exact resolve eq60854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60854
  have eq61136 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61005
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61005
    | exact resolve eq61005 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61005
  have eq61260 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61136
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq61136
    | exact resolve eq61136 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61136
  have eq61376 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq61260
       have r₂ := eq85
       grind)
    | exact resolve eq61260 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq61260
  have eq61425 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61376 eq63
    | exact resolve eq63 eq61376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61376
  have eq61479 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq61425
    | exact resolve eq61425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61425
  have eq75134 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22779 eq22703
    | exact resolve eq22703 eq22779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22703 eq22779
  have eq75235 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq75134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75134
  have eq75641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75235 eq22700
    | exact resolve eq22700 eq75235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22700 eq75235
  have eq75760 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq75641
  have eq75894 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq75760
    | exact resolve eq75760 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75760
  have eq76038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75894 eq28652
    | exact resolve eq28652 eq75894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28652 eq75894
  have eq76136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq76038
  have eq76188 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq76136
       have r₂ := eq27
       grind)
    | exact resolve eq76136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76136
  have eq76229 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76188 eq72
    | (have r₁ := eq72
       have r₂ := eq76188
       grind)
    | exact resolve eq72 eq76188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76236 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76188 eq766
    | exact resolve eq766 eq76188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq76250 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76188 eq3564
    | exact resolve eq3564 eq76188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq76255 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76188 eq11581
    | exact resolve eq11581 eq76188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11581 eq76188
  have eq76259 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq76229
  have eq77344 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76236 eq3562
    | exact resolve eq3562 eq76236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3562 eq76236
  have eq78322 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76250 eq4707
    | exact resolve eq4707 eq76250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78366 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4707 eq78322
    | exact resolve eq78322 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4707 eq78322
  have eq80356 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61479 eq76255
    | exact resolve eq76255 eq61479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61479 eq76255
  have eq80373 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq80356
  have eq82125 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77344 eq76250
    | exact resolve eq76250 eq77344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76250 eq77344
  have eq82216 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq82125
  have eq82440 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq82216 eq78366
    | exact resolve eq78366 eq82216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78366 eq82216
  have eq82541 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq82440
  have eq82781 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq82541 eq57
    | exact resolve eq57 eq82541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82541
  have eq82945 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq849 eq82781
    | exact resolve eq82781 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq82781
  have eq109015 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = (M.op X1 (M.op X1 X1)) ∨ (M.op X1 (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2512 X0 X1 X2
       have i₂ := eq1209 X1 X1
       grind)
    | exact superpose eq1209 eq2512
    | (have j0 := eq2512 X0 X1 X2
       grind)
    | exact resolve eq2512 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq2512
  have eq109016 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 (M.op X0 X1)) ∨ (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109015 X0 X1 x
       have i₂ := eq1192 X1 x X0
       grind)
    | exact superpose eq1192 eq109015
    | (have j0 := eq109015 X0 X1 x
       grind)
    | (have r₁ := eq109015 x x X1
       have r₂ := eq1192 x X1 x
       grind)
    | exact resolve eq109015 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192 eq109015
  have eq145991 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq80373 eq63
    | exact resolve eq63 eq80373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq80373
  have eq146054 : x = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq145991
    | exact resolve eq145991 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq145991
  have eq146055 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq146054
  have eq146080 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq146055
       grind)
    | exact superpose eq146055 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq146055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146092 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq146080
  have eq146113 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq146092
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq146092
    | exact resolve eq146092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146092
  have eq146114 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq146113
  have eq146158 : (M.op x x) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq146114
       grind)
    | exact superpose eq146114 eq56
    | exact resolve eq56 eq146114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146159 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq146114
       grind)
    | exact superpose eq146114 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq146114
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq146114
       grind)
    | exact resolve eq12 eq146114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146160 : x ≠ x ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq146114
       grind)
    | exact superpose eq146114 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq146114
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq146114
       grind)
    | exact resolve eq13 eq146114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146114
  have eq146261 : (k x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq146160
  have eq146262 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq146159
  have eq146324 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq146262
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq146262
    | exact resolve eq146262 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146262
  have eq146325 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq146324
  have eq146498 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq146325
       grind)
    | exact superpose eq146325 eq79
    | exact resolve eq79 eq146325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146325
  have eq146539 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq146498
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq146498
    | exact resolve eq146498 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146498
  have eq146585 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq146539 eq76259
    | exact resolve eq76259 eq146539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76259 eq146539
  have eq146601 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq146585
  have eq146851 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq146601 eq82945
    | exact resolve eq82945 eq146601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82945 eq146601
  have eq146978 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq146851
  have eq147023 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq146978
    | exact resolve eq146978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146978
  have eq169853 : x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq146055
       have i₂ := eq146261
       grind)
    | exact superpose eq146261 eq146055
    | exact resolve eq146055 eq146261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146055 eq146261
  have eq169865 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq169853
  have eq169946 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20338
       have i₂ := eq169865
       grind)
    | exact superpose eq169865 eq20338
    | exact resolve eq20338 eq169865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169974 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 x
       have i₂ := eq169865
       grind)
    | exact superpose eq169865 eq14
    | exact resolve eq14 eq169865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169865
  have eq170150 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq169974 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq169974
    | exact resolve eq169974 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq169974
  have eq170158 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq169946
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq169946
    | exact resolve eq169946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169946
  have eq170261 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170158 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq170158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170158
  have eq170282 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq170261
  have eq172497 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170282 eq57
    | exact resolve eq57 eq170282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170282
  have eq183251 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170150 eq146158
    | exact resolve eq146158 eq170150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146158 eq170150
  have eq183487 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq183251
  have eq183698 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq183487
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq183487
    | exact resolve eq183487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183487
  have eq184341 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20338
       have i₂ := eq183698
       grind)
    | exact superpose eq183698 eq20338
    | exact resolve eq20338 eq183698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183698
  have eq184588 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq184341
    | exact resolve eq184341 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184341
  have eq190195 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq184588 eq58012
    | exact resolve eq58012 eq184588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184588
  have eq198160 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq172497 eq147023
    | exact resolve eq147023 eq172497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147023 eq172497
  have eq198306 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq198160
  have eq198726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq198306 eq190195
    | exact resolve eq190195 eq198306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190195 eq198306
  have eq198862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq198726
  have eq198970 : y = (M.op x y) := by
    first
    | (have r₁ := eq198862
       have r₂ := eq27
       grind)
    | exact resolve eq198862 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198862
  have eq199102 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq198970 eq20
    | exact resolve eq20 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq199105 : y ≠ y ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq198970 eq71
    | (have r₁ := eq71
       have r₂ := eq198970
       grind)
    | exact resolve eq71 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq199108 : y ≠ y ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq198970 eq84
    | (have r₁ := eq84
       have r₂ := eq198970
       grind)
    | exact resolve eq84 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq199168 : (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq198970 eq2290
    | exact resolve eq2290 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq199180 : (M.op y x) = (k (M.op y x) y) := by
    first
    | exact superpose eq198970 eq11473
    | exact resolve eq11473 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11473
  have eq199186 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq199108
  have eq199187 : (k y x) = (M.op y y) := by grind
  clear eq199105
  have eq199243 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq199102
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq199102
    | exact resolve eq199102 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199102
  have eq199284 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq199243 eq26
    | exact resolve eq26 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq200132 : (k (σ y) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq20002
       have i₂ := eq199168
       grind)
    | exact superpose eq199168 eq20002
    | exact resolve eq20002 eq199168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20002
  have eq200284 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
    first
    | exact superpose eq58250 eq200132
    | exact resolve eq200132 eq58250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58250 eq200132
  have eq200304 : (σ (M.op y x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq199243 eq200284
    | exact resolve eq200284 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200284
  have eq200566 : (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq199187
       have i₂ := eq199168
       grind)
    | exact superpose eq199168 eq199187
    | exact resolve eq199187 eq199168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199168 eq199187
  have eq200579 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq200566
       grind)
    | exact superpose eq200566 eq79
    | exact resolve eq79 eq200566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq200566
  have eq200631 : (σ (M.op y x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq199243 eq200579
    | exact resolve eq200579 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200579
  have eq200958 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq200631
       have i₂ := eq200304
       grind)
    | exact superpose eq200304 eq200631
    | exact resolve eq200631 eq200304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200631
  have eq200985 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq200958 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq200958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200999 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq199284 eq200985
    | exact resolve eq200985 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200985
  have eq201010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq199284 eq200999
    | exact resolve eq200999 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200999
  have eq201021 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq201010
       have r₂ := eq27
       grind)
    | exact resolve eq201010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201010
  have eq211120 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x X0)) = (M.op (M.op (M.op X0 X1) X2) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq198970 eq3286
    | exact resolve eq3286 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq211630 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (M.op (M.op X0 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq211120 X0 x x
       have i₂ := eq467 X0 x x y X1
       grind)
    | exact superpose eq467 eq211120
    | exact resolve eq211120 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq211120
  have eq219616 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op x (M.op (M.op X0 X1) (M.op x X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq198970 eq7867
    | exact resolve eq7867 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7867
  have eq220086 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq11467 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq219616 X0 x x
       grind)
    | exact superpose eq219616 eq11467
    | exact resolve eq11467 eq219616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467 eq219616
  have eq220414 : ∀ X0 : G, (M.op y x) = (k (M.op y x) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq198970 eq220086
    | exact resolve eq220086 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220086
  have eq221289 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2978 y x
       have i₂ := eq199186
       grind)
    | exact superpose eq199186 eq2978
    | (have j0 := eq2978 y x
       grind)
    | exact resolve eq2978 eq199186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq221290 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2995 x y
       have i₂ := eq199186
       grind)
    | exact superpose eq199186 eq2995
    | (have j0 := eq2995 x x
       grind)
    | exact resolve eq2995 eq199186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199186
  have eq221295 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq221290
  have eq221296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq221289
  have eq221302 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq221295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq221295
    | exact resolve eq221295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221295
  have eq221303 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq221296
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq221296
    | exact resolve eq221296 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221296
  have eq221326 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq221302
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq221302
    | exact resolve eq221302 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221302
  have eq221327 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq199243 eq221303
    | exact resolve eq221303 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221303
  have eq221346 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq199243 eq221326
    | exact resolve eq221326 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221326
  have eq221347 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq221327
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq221327
    | exact resolve eq221327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221327
  have eq221364 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq221346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq221346
    | exact resolve eq221346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221346
  have eq221365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq199284 eq221347
    | exact resolve eq221347 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221347
  have eq221377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq199284 eq221364
    | exact resolve eq221364 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221364
  have eq221378 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq221365
       have r₂ := eq27
       grind)
    | exact resolve eq221365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221365
  have eq221390 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq221377
       have r₂ := eq27
       grind)
    | exact resolve eq221377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221377
  have eq221391 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq221378
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq221378
    | exact resolve eq221378 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221378
  have eq221403 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq221391
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq221391
    | exact resolve eq221391 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221391
  have eq221415 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq199243 eq221403
    | exact resolve eq221403 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221403
  have eq225735 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq221390 eq14
    | exact resolve eq14 eq221390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225918 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq57 eq225735
    | exact resolve eq225735 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225735
  have eq226027 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq221415 eq57
    | exact resolve eq57 eq221415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221415
  have eq240404 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
    first
    | (have i₁ := eq2979 (M.op y x)
       have i₂ := eq220414 x
       grind)
    | exact superpose eq220414 eq2979
    | (have j0 := eq2979 (M.op y x)
       grind)
    | exact resolve eq2979 eq220414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979
  have eq240425 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by grind
  clear eq240404
  have eq240444 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq240425
       have i₂ := eq200304
       grind)
    | exact superpose eq200304 eq240425
    | exact resolve eq240425 eq200304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240425
  have eq240467 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq240444
       have i₂ := eq14 sF1 (M.op sF1 sF1) sF1
       grind)
    | exact superpose eq14 eq240444
    | exact resolve eq240444 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240444
  have eq240486 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq240467
       have i₂ := eq17314 sF1 sF1 sF1
       grind)
    | exact superpose eq17314 eq240467
    | exact resolve eq240467 eq17314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240467
  have eq240528 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq201021 eq240486
    | exact resolve eq240486 eq201021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240549 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq240486 eq12
    | (have j0 := eq12 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq240486
       grind)
    | exact resolve eq12 eq240486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240699 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by grind
  clear eq240549
  have eq240731 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq240699
       have i₂ := eq14 sF1 sF1 sF1
       grind)
    | exact superpose eq14 eq240699
    | exact resolve eq240699 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240699
  have eq240772 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq240486 eq240731
    | exact resolve eq240731 eq240486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240731
  have eq256380 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq201021 eq240772
    | exact resolve eq240772 eq201021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201021 eq240772
  have eq256404 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq256380
       have r₂ := eq27
       grind)
    | exact resolve eq256380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256380
  have eq256502 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq256404 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq256404
       grind)
    | exact resolve eq12 eq256404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256404
  have eq256639 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq256502
  have eq256734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq199284 eq256639
    | exact resolve eq256639 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256639
  have eq256805 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq256734
       have r₂ := eq27
       grind)
    | exact resolve eq256734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256734
  have eq256839 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq200958 eq256805
    | exact resolve eq256805 eq200958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256805
  have eq295579 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq226027 eq225918
    | exact resolve eq225918 eq226027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225918 eq226027
  have eq295725 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq295579
  have eq295859 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq199284 eq295725
    | exact resolve eq295725 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295725
  have eq296221 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq295859 eq221390
    | exact resolve eq221390 eq295859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221390 eq295859
  have eq296391 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq296221
  have eq296682 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq199180
       have i₂ := eq296391
       grind)
    | exact superpose eq296391 eq199180
    | exact resolve eq199180 eq296391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199180
  have eq296683 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq200304
       have i₂ := eq296391
       grind)
    | exact superpose eq296391 eq200304
    | exact resolve eq200304 eq296391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200304
  have eq296695 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq220414 x
       have i₂ := eq296391
       grind)
    | exact superpose eq296391 eq220414
    | exact resolve eq220414 eq296391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220414 eq296391
  have eq296977 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq296695
       have i₂ := eq20337
       grind)
    | exact superpose eq20337 eq296695
    | exact resolve eq296695 eq20337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20337 eq296695
  have eq296986 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq296683
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq296683
    | exact resolve eq296683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296683
  have eq297305 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2995 x y
       have i₂ := eq296682
       grind)
    | exact superpose eq296682 eq2995
    | (have j0 := eq2995 x x
       grind)
    | exact resolve eq2995 eq296682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995 eq296682
  have eq297310 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq297305
  have eq297317 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq297310
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq297310
    | exact resolve eq297310 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297310
  have eq297339 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq297317
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq297317
    | exact resolve eq297317 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297317
  have eq297359 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199243 eq297339
    | exact resolve eq297339 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297339
  have eq297377 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq297359
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq297359
    | exact resolve eq297359 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq297359
  have eq297390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199284 eq297377
    | exact resolve eq297377 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297377
  have eq297403 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq297390
       have r₂ := eq27
       grind)
    | exact resolve eq297390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297390
  have eq297665 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq211630 x x
       have i₂ := eq296977
       grind)
    | exact superpose eq296977 eq211630
    | exact resolve eq211630 eq296977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211630 eq296977
  have eq297685 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq297665
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq297665
    | exact resolve eq297665 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq297665
  have eq297773 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq198970 eq297685
    | exact resolve eq297685 eq198970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198970 eq297685
  have eq298064 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq296986 eq4645
    | exact resolve eq4645 eq296986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645 eq296986
  have eq298187 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq298064 x
       have i₂ := eq14 sF1 sF4 x
       grind)
    | exact superpose eq14 eq298064
    | exact resolve eq298064 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298064
  have eq298285 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1287 eq298187
    | exact resolve eq298187 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq298187
  have eq298352 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199284 eq298285
    | exact resolve eq298285 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298285
  have eq300446 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20338
       have i₂ := eq297773
       grind)
    | exact superpose eq297773 eq20338
    | exact resolve eq20338 eq297773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20338 eq297773
  have eq300783 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58012 eq300446
    | exact resolve eq300446 eq58012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300446
  have eq300912 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq300783
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq300783
    | exact resolve eq300783 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq300783
  have eq301003 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199243 eq300912
    | exact resolve eq300912 eq199243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199243 eq300912
  have eq310602 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq301003 eq3016
    | exact resolve eq3016 eq301003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301003
  have eq310752 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199284 eq310602
    | exact resolve eq310602 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310602
  have eq323030 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq298352 eq297403
    | exact resolve eq297403 eq298352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297403 eq298352
  have eq323207 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq323030
  have eq323710 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq323207 eq310752
    | exact resolve eq310752 eq323207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310752 eq323207
  have eq323866 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq323710
  have eq324191 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq323866 eq27
    | exact resolve eq27 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq324331 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq323866 eq240528
    | exact resolve eq240528 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240528
  have eq324335 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq323866 eq256839
    | exact resolve eq256839 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256839
  have eq324341 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq324331
  have eq324346 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq200958 eq324335
    | exact resolve eq324335 eq200958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200958 eq324335
  have eq324347 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq324346
  have eq324460 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq324341 eq3016
    | exact resolve eq3016 eq324341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq324470 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq324341 eq6804
    | exact resolve eq6804 eq324341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6804
  have eq324595 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq199284 eq324470
    | exact resolve eq324470 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324470
  have eq324604 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq199284 eq324460
    | exact resolve eq324460 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324460
  have eq324702 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq323866 eq324595
    | exact resolve eq324595 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324595
  have eq324709 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq323866 eq324604
    | exact resolve eq324604 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324604
  have eq324797 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq324341 eq324702
    | exact resolve eq324702 eq324341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324702
  have eq324802 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq324341 eq324709
    | exact resolve eq324709 eq324341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324709
  have eq325105 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq324347 eq6754
    | exact resolve eq6754 eq324347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6754
  have eq325211 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq199284 eq325105
    | exact resolve eq325105 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325105
  have eq325281 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq323866 eq325211
    | exact resolve eq325211 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325211
  have eq325319 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq324341 eq325281
    | exact resolve eq325281 eq324341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325281
  have eq328398 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) ≠ (M.op (σ (M.op x y)) (M.op (M.op (σ x) X0) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (M.op (σ x) X0) (σ (M.op x y)))) (M.op (M.op (σ x) X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq325319 eq109016
    | (have j0 := eq109016 (M.op (σ x) X0) (σ (M.op x y))
       grind)
    | exact resolve eq109016 eq325319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109016
  have eq328467 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) ≠ (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (M.op (σ x) X0) (σ (M.op x y)))) (M.op (M.op (σ x) X0) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq328398 x
       have i₂ := eq17314 sF1 sF2 x
       grind)
    | exact superpose eq17314 eq328398
    | (have j0 := eq328398 X0
       grind)
    | exact resolve eq328398 eq17314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17314 eq328398
  have eq328646 : ∀ X0 : G, (σ x) ≠ (M.op (M.op (σ x) X0) (σ x)) ∨ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (M.op (σ x) X0) (σ (M.op x y)))) (M.op (M.op (σ x) X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq325319 eq328467
    | (have j0 := eq328467 X0
       grind)
    | exact resolve eq328467 eq325319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325319 eq328467
  have eq328788 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (M.op (σ x) X0) (σ (M.op x y)))) (M.op (M.op (σ x) X0) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq328646 x
       have i₂ := eq14 sF2 sF2 x
       grind)
    | exact superpose eq14 eq328646
    | (have j0 := eq328646 X0
       grind)
    | exact resolve eq328646 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328646
  have eq328905 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (M.op (σ x) X0) (σ (M.op x y)))) (M.op (M.op (σ x) X0) (σ (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq328788 X0
       grind)
    | (have r₁ := eq328788 X0
       have r₂ := eq324797 (σ x)
       grind)
    | exact resolve eq328788 eq324797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324797 eq328788
  have eq328984 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ (M.op x y)) (σ x)))) (M.op (σ x) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | (have i₁ := eq328905 x
       have i₂ := eq14 sF2 sF1 x
       grind)
    | exact superpose eq14 eq328905
    | exact resolve eq328905 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328905
  have eq329038 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq57 eq328984
    | exact resolve eq328984 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq328984
  have eq329078 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) (M.op (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq323866 eq329038
    | exact resolve eq329038 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329038
  have eq329112 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq199284 eq329078
    | exact resolve eq329078 eq199284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199284 eq329078
  have eq329143 : (k (M.op (σ (M.op x y)) (σ x)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq323866 eq329112
    | exact resolve eq329112 eq323866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323866 eq329112
  have eq329171 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq240486 eq329143
    | exact resolve eq329143 eq240486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240486 eq329143
  have eq329192 : (k (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq324341 eq329171
    | exact resolve eq329171 eq324341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324341 eq329171
  have eq329210 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq324347 eq329192
    | exact resolve eq329192 eq324347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324347 eq329192
  have eq329223 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq58012 eq329210
    | exact resolve eq329210 eq58012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58012 eq329210
  have eq329235 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq324802 eq329223
    | exact resolve eq329223 eq324802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324802 eq329223
  have eq329245 : False := by grind
  exact eq329245

/-- `Equation4440`: `x ◇ (y ◇ x) = (x ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation4440 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4440 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4440.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq213 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7880 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq16
    | (have j1 := eq214 y y
       grind)
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7883 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X1 (σ X0)
       have i₂ := eq214 X0 X0
       grind)
    | exact superpose eq214 eq213
    | (have j0 := eq213 X1 (σ X0)
       have j1 := eq214 X0 X0
       grind)
    | (have r₁ := eq213 X0 (σ X1)
       have r₂ := eq214 X0 X1
       grind)
    | (have r₁ := eq213 X0 (σ X0)
       have r₂ := eq214 X0 X1
       grind)
    | exact resolve eq213 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7884 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq214 X0 X0
       grind)
    | exact superpose eq214 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq214 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq214 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq214 X0 X1
       grind)
    | exact resolve eq12 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7886 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq214 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq7887 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7886
  have eq7889 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7884 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7884
  have eq7890 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7883
  have eq7893 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7889 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq7889 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq7889 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7889
  have eq7894 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq7890 X0 X1
       have j1 := eq213 X1 (σ X0)
       grind)
    | (have r₁ := eq7890 X0 X1
       have r₂ := eq213 X0 (σ X0)
       grind)
    | exact resolve eq7890 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7890
  have eq7917 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7887 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq7887
    | (have j0 := eq7887 (τ X0)
       grind)
    | exact resolve eq7887 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq7887
  have eq7929 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7917 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7917
    | (have j0 := eq7917 X0
       grind)
    | exact resolve eq7917 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7917
  have eq7946 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7929 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7929
    | (have j0 := eq7929 X0
       grind)
    | exact resolve eq7929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7929
  have eq7981 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7946 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq7946
    | (have j0 := eq7946 (τ X0)
       grind)
    | exact resolve eq7946 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7946
  have eq9288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7880
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq7880
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq7880 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq9291 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq9288
  have eq9527 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq213 X0 (σ y)
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq213
    | (have j0 := eq213 X0 (σ y)
       grind)
    | (have r₁ := eq213 X0 (σ y)
       have r₂ := eq9291
       grind)
    | (have r₁ := eq213 X0 (σ x)
       have r₂ := eq9291
       grind)
    | (have r₁ := eq213 X0 y
       have r₂ := eq9291
       grind)
    | exact resolve eq213 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9528 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq9527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9527
  have eq9899 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7981 (σ y)
       have i₂ := eq9528 (σ y)
       grind)
    | exact superpose eq9528 eq7981
    | (have j0 := eq7981 (σ y)
       grind)
    | exact resolve eq7981 eq9528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9528
  have eq10019 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9899
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9899
    | exact resolve eq9899 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9899
  have eq10030 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10019
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10019
    | exact resolve eq10019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019
  have eq10031 : y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10030
  have eq10034 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10031
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq10031
    | exact resolve eq10031 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9291 eq10031
  have eq10043 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10034
  have eq10044 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10043
       have r₂ := eq10 y
       grind)
    | exact resolve eq10043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10043
  have eq10047 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq213 X0 (σ x)
       have i₂ := eq10044
       grind)
    | exact superpose eq10044 eq213
    | (have j0 := eq213 X0 (σ x)
       grind)
    | (have r₁ := eq213 X0 (σ x)
       have r₂ := eq10044
       grind)
    | (have r₁ := eq213 X0 y
       have r₂ := eq10044
       grind)
    | (have r₁ := eq213 X0 x
       have r₂ := eq10044
       grind)
    | exact resolve eq213 eq10044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10048 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10047 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10047
  have eq10085 : (τ (M.op (σ x) (σ x))) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7981 (σ x)
       have i₂ := eq10048 (σ x)
       grind)
    | exact superpose eq10048 eq7981
    | (have j0 := eq7981 (σ x)
       grind)
    | exact resolve eq7981 eq10048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7981 eq10048
  have eq10205 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10085
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10085
    | exact resolve eq10085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10085
  have eq10216 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10205
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10205
    | exact resolve eq10205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205
  have eq10217 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq10216
  have eq10220 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10217
       have i₂ := eq10044
       grind)
    | exact superpose eq10044 eq10217
    | exact resolve eq10217 eq10044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10044 eq10217
  have eq10229 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq10220
  have eq10230 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10229
       have r₂ := eq10 x
       grind)
    | exact resolve eq10229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10229
  have eq10231 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10230
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq10230
       grind)
    | exact resolve eq12 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10232 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq213 X0 y
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq213
    | (have j0 := eq213 X0 y
       grind)
    | (have r₁ := eq213 X0 y
       have r₂ := eq10230
       grind)
    | (have r₁ := eq213 X0 x
       have r₂ := eq10230
       grind)
    | exact resolve eq213 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10233 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10232
  have eq10234 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10231
  have eq10291 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op y (σ X0))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq10233 (σ X0)
       grind)
    | exact superpose eq10233 eq28
    | exact resolve eq28 eq10233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq10387 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op (σ X0) y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq10234 (σ X0)
       grind)
    | exact superpose eq10234 eq22
    | exact resolve eq22 eq10234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq10403 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18 X0 y
       have i₂ := eq10234 (τ X0)
       grind)
    | exact superpose eq10234 eq18
    | exact resolve eq18 eq10234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10234
  have eq10431 : ∀ X0 : G, (τ (M.op y X0)) = (k (τ X0) (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10291 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10291
    | exact resolve eq10291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10291
  have eq10507 : ∀ X0 : G, (τ (k X0 y)) = (τ (M.op y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10431 X0
       have i₂ := eq31 y X0
       grind)
    | exact superpose eq31 eq10431
    | exact resolve eq10431 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10431
  have eq10542 : ∀ X0 X1 : G, (τ (k (k X0 y) X1)) = (k (τ (M.op y X0)) (τ X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (k X0 y)
       have i₂ := eq10507 X0
       grind)
    | exact superpose eq10507 eq31
    | exact resolve eq31 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10631 : ∀ X0 X1 : G, (τ (k (k X0 y) X1)) = (τ (k (M.op y X0) X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq10542 X0 X1
       have i₂ := eq31 X1 (M.op y X0)
       grind)
    | exact superpose eq31 eq10542
    | exact resolve eq10542 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10542
  have eq10861 : ∀ X0 : G, (τ (M.op X0 y)) = (k (τ y) (τ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10387 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10387
    | exact resolve eq10387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10387
  have eq10942 : ∀ X0 : G, (τ (M.op X0 y)) = (τ (k y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10861 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq10861
    | exact resolve eq10861 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10861
  have eq10976 : ∀ X0 X1 : G, (τ (k X1 (k y X0))) = (k (τ X1) (τ (M.op X0 y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (k y X0) X1
       have i₂ := eq10942 X0
       grind)
    | exact superpose eq10942 eq31
    | exact resolve eq31 eq10942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10942
  have eq11069 : ∀ X0 X1 : G, (τ (k X1 (M.op X0 y))) = (τ (k X1 (k y X0))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq10976 X0 X1
       have i₂ := eq31 (M.op X0 y) X1
       grind)
    | exact superpose eq31 eq10976
    | exact resolve eq10976 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10976
  have eq11080 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10403 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10403
    | exact resolve eq10403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10403
  have eq11166 : ∀ X0 : G, (σ (M.op X0 y)) = (σ (k y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11080 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq11080
    | exact resolve eq11080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11080
  have eq11350 : ∀ X0 : G, (τ (k (M.op y X0) y)) = (τ (M.op y (k X0 y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10507 (k X0 y)
       have i₂ := eq10631 X0 y
       grind)
    | exact superpose eq10631 eq10507
    | exact resolve eq10507 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507 eq10631
  have eq11408 : ∀ X0 : G, (τ (k (M.op y X0) y)) = (τ (M.op y (k X0 y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq11350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11350
  have eq12995 : ∀ X0 X1 : G, (k X0 (k y X1)) = (σ (τ (k X0 (M.op X1 y)))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (k y X1))
       have i₂ := eq11069 X1 X0
       grind)
    | exact superpose eq11069 eq11
    | exact resolve eq11 eq11069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq13107 : ∀ X0 X1 : G, (k X0 (M.op X1 y)) = (k X0 (k y X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq12995 X0 X1
       have i₂ := eq11 (k X0 (M.op X1 y))
       grind)
    | exact superpose eq11 eq12995
    | exact resolve eq12995 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12995
  have eq13747 : (τ (k y y)) = (τ (M.op y (k y y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11408 y
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq11408
    | exact resolve eq11408 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11408
  have eq13830 : (τ (k y y)) = (τ (M.op y (k y y))) ∨ x = (M.op x x) := by grind
  clear eq13747
  have eq13877 : (τ (M.op y y)) = (τ (M.op y (M.op y y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13830
       have i₂ := eq10233 y
       grind)
    | exact superpose eq10233 eq13830
    | exact resolve eq13830 eq10233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13830
  have eq13941 : (τ (M.op y y)) = (τ (M.op y (M.op y y))) ∨ x = (M.op x x) := by grind
  clear eq13877
  have eq13988 : (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13941
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq13941
    | exact resolve eq13941 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13941
  have eq14048 : (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq13988
  have eq14104 : ∀ X0 : G, (k (τ y) (τ X0)) = (τ (k (M.op y y) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op y y)
       have i₂ := eq14048
       grind)
    | exact superpose eq14048 eq31
    | exact resolve eq31 eq14048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14048
  have eq14203 : ∀ X0 : G, (τ (k y X0)) = (τ (k (M.op y y) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14104 X0
       have i₂ := eq31 X0 y
       grind)
    | exact superpose eq31 eq14104
    | exact resolve eq14104 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14104
  have eq14363 : ∀ X0 : G, (σ (τ (k y X0))) = (k (M.op y y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op y y) X0)
       have i₂ := eq14203 X0
       grind)
    | exact superpose eq14203 eq11
    | exact resolve eq11 eq14203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14203
  have eq14479 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14363 X0
       have i₂ := eq11 (k y X0)
       grind)
    | exact superpose eq11 eq14363
    | exact resolve eq14363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14363
  have eq14597 : ∀ X0 : G, (k y (k y X0)) = (k (M.op y y) (M.op X0 y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13107 (M.op y y) X0
       have i₂ := eq14479 (k y X0)
       grind)
    | exact superpose eq14479 eq13107
    | exact resolve eq13107 eq14479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13107 eq14479
  have eq14622 : ∀ X0 : G, (k y (k y X0)) = (k (M.op y y) (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq14597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597
  have eq32534 : (k y y) = (k y (k y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14622 y
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq14622
    | exact resolve eq14622 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14622
  have eq32600 : (k y y) = (k y (k y y)) ∨ x = (M.op x x) := by grind
  clear eq32534
  have eq32640 : (M.op y y) = (k y (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32600
       have i₂ := eq10233 y
       grind)
    | exact superpose eq10233 eq32600
    | exact resolve eq32600 eq10233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10233 eq32600
  have eq32755 : (M.op y y) = (k y (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq32640
  have eq32757 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32755
       have i₂ := eq10230
       grind)
    | exact superpose eq10230 eq32755
    | exact resolve eq32755 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10230 eq32755
  have eq32874 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq32757
  have eq32967 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7893 y X0
       have i₂ := eq32874
       grind)
    | exact superpose eq32874 eq7893
    | (have j0 := eq7893 y X0
       grind)
    | exact resolve eq7893 eq32874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893 eq32874
  have eq33060 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq32967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32967
  have eq33958 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq33060 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq33060
    | exact resolve eq33060 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33060
  have eq35813 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33958 x
       grind)
    | exact superpose eq33958 eq16
    | exact resolve eq16 eq33958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33958
  have eq35884 : x = (M.op x x) := by
    first
    | (have r₁ := eq35813
       have r₂ := eq11166 x
       grind)
    | exact resolve eq35813 eq11166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11166 eq35813
  have eq35887 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq213 X0 x
       have i₂ := eq35884
       grind)
    | exact superpose eq35884 eq213
    | (have j0 := eq213 X0 x
       grind)
    | (have r₁ := eq213 X0 x
       have r₂ := eq35884
       grind)
    | exact resolve eq213 eq35884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq35888 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq35887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35887
  have eq35908 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7894 x X0
       have i₂ := eq35888 x
       grind)
    | exact superpose eq35888 eq7894
    | (have j0 := eq7894 x X0
       grind)
    | exact resolve eq7894 eq35888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894
  have eq36052 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq35908 X0
       have i₂ := eq35884
       grind)
    | exact superpose eq35884 eq35908
    | (have j0 := eq35908 X0
       grind)
    | exact resolve eq35908 eq35884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35884 eq35908
  have eq36053 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq36052 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36052
  have eq36912 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq36053 (σ X0)
       grind)
    | exact superpose eq36053 eq15
    | exact resolve eq15 eq36053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36053
  have eq37004 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq36912 X0
       have i₂ := eq35888 X0
       grind)
    | exact superpose eq35888 eq36912
    | exact resolve eq36912 eq35888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35888 eq36912
  have eq38386 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37004 y
       grind)
    | exact superpose eq37004 eq16
    | (have r₁ := eq16
       have r₂ := eq37004 y
       grind)
    | exact resolve eq16 eq37004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37004
  have eq38409 : False := by grind
  exact eq38409

/-- `Equation4467`: `x ◇ (y ◇ x) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4467 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4467 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4467.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
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
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq318 : ∀ X0 : G, (k (k (σ x) (σ y)) (σ X0)) = (σ (k (k x y) X0)) := by
    intro X0
    first
    | exact superpose eq99 eq35
    | exact resolve eq35 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq604 : ∀ X0 : G, (τ (k (k (σ x) (σ y)) X0)) = (k (k x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq99 eq427
    | exact resolve eq427 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq427
  have eq692 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) X5) := by
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
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x y) y) := by
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
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
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
  have eq696 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq692 x x X2 X3 X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq692
    | exact resolve eq692 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq699 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq696 x x X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq696
    | exact resolve eq696 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq700 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (M.op X0 X1) (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 (M.op X0 X1) X1
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq693 x x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op X0 X1) (M.op (M.op x y) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2 X3
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq728 eq699
    | exact resolve eq699 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq699 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq699 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq28 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq770 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq728 eq765
    | exact resolve eq765 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq775 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq770 eq35
    | exact resolve eq35 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq788 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq775 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq775
    | exact resolve eq775 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq801 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k (M.op X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X0 X1
       have i₂ := eq11 (M.op X0 X1) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq699 x
       have i₂ := eq11 (M.op sF4 sF3) x
       grind)
    | exact superpose eq11 eq699
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq840 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq850 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq811 X0
       have j1 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq811 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq811 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq811 x
       have r₂ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) x
       grind)
    | exact resolve eq811 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq851 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq810 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq810
    | (have j0 := eq810 X0 X1 x x
       grind)
    | exact resolve eq810 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq855 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq805
    | (have j0 := eq805 X1 X1 x x
       grind)
    | exact resolve eq805 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq857 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq840 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq840 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq867 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq850 X0
       have j1 := eq28 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq850 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq850 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq868 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (M.op X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq728 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq869 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq728 eq855
    | (have j0 := eq855 X1 X1
       grind)
    | exact resolve eq855 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq872 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq728 eq867
    | exact resolve eq867 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq875 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq829 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq829
    | (have j0 := eq829 (σ X0)
       grind)
    | exact resolve eq829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq788 eq829
    | (have j0 := eq829 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq829 (σ (M.op (M.op x y) y))
       have r₂ := eq788 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq829 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq921 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq908
  have eq998 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 (M.op x X0)
       have i₂ := eq706 x X0
       grind)
    | (have i₁ := eq693 y (M.op x y)
       have i₂ := eq706 x x
       grind)
    | exact superpose eq706 eq693
    | exact resolve eq693 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) := by
    first
    | exact superpose eq872 eq42
    | exact resolve eq42 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) y) := by
    first
    | exact superpose eq872 eq153
    | exact resolve eq153 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2918 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq814
       grind)
    | exact superpose eq814 eq41
    | exact resolve eq41 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2919 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2918
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2918
    | exact resolve eq2918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918
  have eq2921 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2919
    | exact resolve eq2919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq5413 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1) X1
       have i₂ := eq869 X0 X1
       grind)
    | exact superpose eq869 eq11
    | (have j0 := eq11 X1 X1
       have j1 := eq869 X1 X1
       grind)
    | exact resolve eq11 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5434 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5413
  have eq5522 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op X0 (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 (M.op X0 sF0)
       have i₂ := eq868 X0 sF0
       grind)
    | exact superpose eq868 eq42
    | (have j1 := eq868 X0 (M.op x y)
       grind)
    | exact resolve eq42 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq868
  have eq21134 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq921 eq706
    | exact resolve eq706 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21135 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq921 eq708
    | exact resolve eq708 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq21142 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq921 eq21135
    | exact resolve eq21135 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21135
  have eq21157 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq700 eq21142
    | exact resolve eq21142 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21142
  have eq21213 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq21157 eq15
    | exact resolve eq15 eq21157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2921 eq821
    | exact resolve eq821 eq2921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23785 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23777
       have r₂ := eq27
       grind)
    | exact resolve eq23777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23777
  have eq23792 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23785 eq218
    | exact resolve eq218 eq23785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23785
  have eq23829 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23792
    | exact resolve eq23792 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23792
  have eq23842 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23829
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq23829
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq23829
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23829 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23829
  have eq23849 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23842 eq200
    | exact resolve eq200 eq23842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq23842
  have eq23887 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23849
    | exact resolve eq23849 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23849
  have eq23896 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq857 y x
       grind)
    | (have r₁ := eq23887
       have r₂ := eq857 y x
       grind)
    | exact resolve eq23887 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23887
  have eq23899 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq23896
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23896 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23896
  have eq23903 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq814
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq814
    | exact resolve eq814 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq23905 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq41
    | exact resolve eq41 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23906 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq869 x y
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq869
    | (have j0 := eq869 y y
       grind)
    | exact resolve eq869 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23907 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23906
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23906
    | exact resolve eq23906 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23906
  have eq23908 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq23905
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23905
    | exact resolve eq23905 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23905
  have eq23915 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23908 eq2921
    | exact resolve eq2921 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq23918 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23908 eq821
    | exact resolve eq821 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq23922 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23908 eq869
    | (have j0 := eq869 (σ y) (σ y)
       grind)
    | exact resolve eq869 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq23923 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq23922
    | exact resolve eq23922 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23922
  have eq23929 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23918 eq23923
    | exact resolve eq23923 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23923
  have eq23934 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq23903
       grind)
    | exact superpose eq23903 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq23903
       grind)
    | exact resolve eq28 eq23903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23949 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23903
       grind)
    | exact superpose eq23903 eq706
    | exact resolve eq706 eq23903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23952 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq23934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23934
  have eq23955 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23903 eq23949
    | exact resolve eq23949 eq23903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23903 eq23949
  have eq23988 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq23915
       grind)
    | exact superpose eq23915 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq23915
       grind)
    | exact resolve eq28 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24003 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23915
       grind)
    | exact superpose eq23915 eq706
    | exact resolve eq706 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24006 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq23988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23988
  have eq24009 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23915 eq24003
    | exact resolve eq24003 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23915 eq24003
  have eq24040 : y = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23918 eq218
    | exact resolve eq218 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq24057 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23918 eq706
    | exact resolve eq706 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24064 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq23918 eq24057
    | exact resolve eq24057 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23918 eq24057
  have eq24077 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq24040
    | exact resolve eq24040 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24040
  have eq24106 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq23952 X0
       grind)
    | exact superpose eq23952 eq693
    | (have j1 := eq23952 X0
       grind)
    | exact resolve eq693 eq23952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23952
  have eq24127 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24106 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24106
    | (have j0 := eq24106 X0
       grind)
    | exact resolve eq24106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24106
  have eq24175 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq23955 eq998
    | exact resolve eq998 eq23955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24227 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23955 eq21157
    | exact resolve eq21157 eq23955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24264 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24227
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24227
    | exact resolve eq24227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24227
  have eq24421 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq24264
       grind)
    | exact superpose eq24264 eq693
    | exact resolve eq693 eq24264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24442 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24421
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24421
    | exact resolve eq24421 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24421
  have eq24482 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq24442 eq872
    | exact resolve eq872 eq24442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24561 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq24442 eq700
    | exact resolve eq700 eq24442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq26602 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq24006 X0
       grind)
    | exact superpose eq24006 eq693
    | (have j1 := eq24006 X0
       grind)
    | exact resolve eq693 eq24006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24006
  have eq26623 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26602 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26602
    | (have j0 := eq26602 X0
       grind)
    | exact resolve eq26602 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26602
  have eq26673 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq24009 eq998
    | exact resolve eq998 eq24009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26725 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24009 eq21157
    | exact resolve eq21157 eq24009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24009
  have eq26764 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq26725
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26725
    | exact resolve eq26725 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26725
  have eq26921 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq26764
       grind)
    | exact superpose eq26764 eq693
    | exact resolve eq693 eq26764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26764
  have eq26942 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq26921
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26921
    | exact resolve eq26921 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26921
  have eq27044 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq26942 eq21157
    | exact resolve eq21157 eq26942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27080 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq27044
    | exact resolve eq27044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27044
  have eq27419 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by grind
  have eq28758 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq24064 eq693
    | exact resolve eq693 eq24064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24064
  have eq28780 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26 eq28758
    | exact resolve eq28758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28758
  have eq28808 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq24077 eq693
    | exact resolve eq693 eq24077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24077
  have eq28830 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq26 eq28808
    | exact resolve eq28808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28808
  have eq28870 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0
       have i₂ := eq24127 (M.op sF0 y)
       grind)
    | exact superpose eq24127 eq872
    | (have j1 := eq24127 X1
       grind)
    | exact resolve eq872 eq24127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq24127
  have eq29006 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq24482 eq28870
    | (have j0 := eq28870 X0 X1
       have j1 := eq24482 X0
       grind)
    | exact resolve eq28870 eq24482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24482 eq28870
  have eq30665 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq24175 X0
       grind)
    | exact superpose eq24175 eq693
    | (have j1 := eq24175 X0
       grind)
    | exact resolve eq693 eq24175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24175
  have eq30688 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq30665 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30665
    | (have j0 := eq30665 X0
       grind)
    | exact resolve eq30665 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30665
  have eq30705 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq24442 eq30688
    | exact resolve eq30688 eq24442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24442 eq30688
  have eq31099 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1038
       have i₂ := eq26623 (M.op sF0 y)
       grind)
    | exact superpose eq26623 eq1038
    | (have j1 := eq26623 X0
       grind)
    | exact resolve eq1038 eq26623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq31146 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq21157
       have i₂ := eq26623 (M.op sF0 y)
       grind)
    | exact superpose eq26623 eq21157
    | (have j1 := eq26623 X0
       grind)
    | exact resolve eq21157 eq26623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26623
  have eq31184 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq31146
    | (have j0 := eq31146 X0
       grind)
    | exact resolve eq31146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31146
  have eq31209 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq31099
    | (have j0 := eq31099 X0
       grind)
    | exact resolve eq31099 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31099
  have eq31243 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq27080 eq31184
    | exact resolve eq31184 eq27080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31184
  have eq31266 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31243 eq829
    | (have j0 := eq829 (σ y)
       grind)
    | (have r₁ := eq829 (σ y)
       have r₂ := eq31243 (σ y)
       grind)
    | exact resolve eq829 eq31243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31348 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq31266
  have eq31503 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31348 eq706
    | exact resolve eq706 eq31348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31510 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27080 eq31503
    | exact resolve eq31503 eq27080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27080 eq31503
  have eq31525 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31348 eq31510
    | exact resolve eq31510 eq31348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31348 eq31510
  have eq32447 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq26673 X0
       grind)
    | exact superpose eq26673 eq693
    | (have j1 := eq26673 X0
       grind)
    | exact resolve eq693 eq26673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26673
  have eq32470 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq32447 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32447
    | (have j0 := eq32447 X0
       grind)
    | exact resolve eq32447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32447
  have eq32487 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq26942 eq32470
    | exact resolve eq32470 eq26942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26942 eq32470
  have eq37669 : ∀ X0 : G, (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq28780 eq770
    | exact resolve eq770 eq28780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28780
  have eq38095 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq28830 eq1041
    | exact resolve eq1041 eq28830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq28830
  have eq38237 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq857 y (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq38095
       have r₂ := eq857 y x
       grind)
    | exact resolve eq38095 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38095
  have eq38453 : (σ (τ (M.op (σ x) (σ y)))) = (k (σ (τ (M.op (σ x) (σ y)))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38237 eq41
    | exact resolve eq41 eq38237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq38237
  have eq38463 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38453
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq38453
    | exact resolve eq38453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38453
  have eq39283 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (σ y)) := by
    first
    | (have j0 := eq29006 (σ y) (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29006
  have eq39284 : (M.op x y) = (k (M.op x y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39283
  have eq39859 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq318 y
       have i₂ := eq5434 x y
       grind)
    | exact superpose eq5434 eq318
    | (have j1 := eq5434 x y
       grind)
    | exact resolve eq318 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq39871 : (τ (M.op (M.op x y) y)) = (k (k x y) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 sF3
       have i₂ := eq5434 sF2 sF3
       grind)
    | exact superpose eq5434 eq604
    | (have j1 := eq5434 (σ x) (σ y)
       grind)
    | exact resolve eq604 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq5434
  have eq40167 : (τ (M.op (M.op x y) y)) = (k (k x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq39871
    | exact resolve eq39871 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39871
  have eq40179 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39859
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39859
    | exact resolve eq39859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39859
  have eq40336 : (k x y) = (τ (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40167
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq40167
    | exact resolve eq40167 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40167
  have eq40348 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23908 eq40179
    | exact resolve eq40179 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40179
  have eq40389 : (k x y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21213 eq40336
    | exact resolve eq40336 eq21213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40336
  have eq40392 : (k (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21157 eq40348
    | exact resolve eq40348 eq21157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40348
  have eq40411 : x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40389
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq40389
    | exact resolve eq40389 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40389
  have eq40413 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23908 eq40392
    | exact resolve eq40392 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40392
  have eq40426 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23908 eq40411
    | exact resolve eq40411 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23908 eq40411
  have eq40427 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq40426
  have eq40428 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40413
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq40413
    | exact resolve eq40413 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23899 eq40413
  have eq40429 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq40428
  have eq40436 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23929 eq40427
    | exact resolve eq40427 eq23929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23929 eq40427
  have eq40437 : y = (M.op y y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23907 eq40429
    | exact resolve eq40429 eq23907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23907 eq40429
  have eq40876 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40436 eq706
    | exact resolve eq706 eq40436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40883 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq40436 eq40876
    | exact resolve eq40876 eq40436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40436 eq40876
  have eq40917 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq40437
       grind)
    | exact superpose eq40437 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq40437
       grind)
    | exact resolve eq28 eq40437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40932 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq40437
       grind)
    | exact superpose eq40437 eq706
    | exact resolve eq706 eq40437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40935 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq40917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40917
  have eq40938 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40437 eq40932
    | exact resolve eq40932 eq40437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40437 eq40932
  have eq41029 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq40883 eq693
    | exact resolve eq693 eq40883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40883
  have eq41051 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26 eq41029
    | exact resolve eq41029 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41029
  have eq41130 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq40935 X0
       grind)
    | exact superpose eq40935 eq693
    | (have j1 := eq40935 X0
       grind)
    | exact resolve eq693 eq40935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40935
  have eq41151 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq41130 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41130
    | (have j0 := eq41130 X0
       grind)
    | exact resolve eq41130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41130
  have eq41191 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq40938 eq751
    | exact resolve eq751 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41203 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40938 eq921
    | exact resolve eq921 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41265 : y = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40938 eq21157
    | exact resolve eq21157 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41288 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq40938 eq695
    | exact resolve eq695 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq40938
  have eq41309 : (M.op y y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41288 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq41288
    | exact resolve eq41288 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq41288
  have eq41317 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq41265
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41265
    | exact resolve eq41265 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41265
  have eq41376 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41203
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41203
    | exact resolve eq41203 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41203
  have eq41394 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq728 eq41309
    | exact resolve eq41309 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41309
  have eq41426 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq41317 eq41394
    | exact resolve eq41394 eq41317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41394
  have eq41449 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq41376 eq41426
    | exact resolve eq41426 eq41376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41376 eq41426
  have eq41530 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq41317
       grind)
    | exact superpose eq41317 eq693
    | exact resolve eq693 eq41317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41551 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq41530
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41530
    | exact resolve eq41530 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41530
  have eq41590 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq41551 eq751
    | exact resolve eq751 eq41551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41664 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq41551 eq21157
    | exact resolve eq21157 eq41551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41710 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq41664
    | exact resolve eq41664 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41664
  have eq41789 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | (have r₁ := eq41710
       have r₂ := eq27419
       grind)
    | exact resolve eq41710 eq27419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27419 eq41710
  have eq41850 : (M.op x y) = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq41789 eq29
    | exact resolve eq29 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq50568 : ∀ X0 : G, (σ y) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq41051 eq770
    | exact resolve eq770 eq41051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51616 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq921
       have i₂ := eq41151 (M.op sF0 y)
       grind)
    | exact superpose eq41151 eq921
    | (have j1 := eq41151 X0
       grind)
    | exact resolve eq921 eq41151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51678 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq21157
       have i₂ := eq41151 (M.op sF0 y)
       grind)
    | exact superpose eq41151 eq21157
    | (have j1 := eq41151 X0
       grind)
    | exact resolve eq21157 eq41151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41151
  have eq51736 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq51678
    | (have j0 := eq51678 X0
       grind)
    | exact resolve eq51678 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51678
  have eq51770 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq51616
    | (have j0 := eq51616 X0
       grind)
    | exact resolve eq51616 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51616
  have eq51803 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq41789 eq51736
    | exact resolve eq51736 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51736
  have eq52008 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq51803 eq829
    | (have j0 := eq829 (σ y)
       grind)
    | (have r₁ := eq829 (σ y)
       have r₂ := eq51803 (σ y)
       grind)
    | exact resolve eq829 eq51803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52099 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq52008
  have eq53058 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq693 X0 y
       have i₂ := eq41191 X0
       grind)
    | exact superpose eq41191 eq693
    | exact resolve eq693 eq41191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41191
  have eq53111 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq41317 eq53058
    | exact resolve eq53058 eq41317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41317 eq53058
  have eq53137 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq41449 eq53111
    | exact resolve eq53111 eq41449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41449 eq53111
  have eq57592 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0
       have i₂ := eq50568 (M.op sF0 y)
       grind)
    | exact superpose eq50568 eq998
    | (have j1 := eq50568 X1
       grind)
    | exact resolve eq998 eq50568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998 eq50568
  have eq66265 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53137 eq26
    | (have j1 := eq53137 (σ x)
       grind)
    | exact resolve eq26 eq53137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53137
  have eq66398 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq66265
       grind)
    | exact superpose eq66265 eq693
    | exact resolve eq693 eq66265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66419 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66398
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66398
    | exact resolve eq66398 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66398
  have eq66545 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66419 eq21157
    | exact resolve eq21157 eq66419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66602 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq66545
    | exact resolve eq66545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66545
  have eq66892 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq66602 eq699
    | exact resolve eq699 eq66602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66986 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq52099 eq66892
    | exact resolve eq66892 eq52099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52099 eq66892
  have eq68367 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) (σ y)) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq66986 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq66986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66986
  have eq68451 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq68367 X0
       have j1 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq68367 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq68367 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq68367 x
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq68367 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68367
  have eq68486 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq68451 X0
       have j1 := eq28 (σ y) X0
       grind)
    | (have r₁ := eq68451 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq68451 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68451
  have eq72403 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq57592 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq57592 eq26
    | (have j1 := eq57592 (σ x) X0
       grind)
    | exact resolve eq26 eq57592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57592
  have eq72513 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72403 eq829
    | (have j0 := eq829 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq829 (M.op (σ x) (σ y))
       have r₂ := eq72403 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq829 eq72403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72403
  have eq72575 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72513
  have eq72710 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72575 eq706
    | exact resolve eq706 eq72575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72718 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72575 eq72710
    | exact resolve eq72710 eq72575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72575 eq72710
  have eq72862 : y = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72718 eq23955
    | exact resolve eq23955 eq72718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23955
  have eq72940 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24264 eq72862
    | exact resolve eq72862 eq24264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24264 eq72862
  have eq72941 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (σ x) := by grind
  clear eq72940
  have eq73034 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66265 eq72941
    | exact resolve eq72941 eq66265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66265 eq72941
  have eq73035 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq73034
  have eq74559 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq73035
       grind)
    | exact superpose eq73035 eq693
    | exact resolve eq693 eq73035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73035
  have eq74580 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74559
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74559
    | exact resolve eq74559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74559
  have eq74725 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74580 eq72718
    | exact resolve eq72718 eq74580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72718 eq74580
  have eq74747 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq74725
  have eq77776 : (M.op x y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq74747
  have eq83592 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq829 X0
       have i₂ := eq31209 (k X0 X0)
       grind)
    | exact superpose eq31209 eq829
    | (have j0 := eq829 (σ (M.op x y))
       have j1 := eq31209 X0
       grind)
    | (have r₁ := eq829 (σ (M.op x y))
       have r₂ := eq31209 X0
       grind)
    | (have r₁ := eq829 y
       have r₂ := eq31209 y
       grind)
    | exact resolve eq829 eq31209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31209
  have eq83614 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq83592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83592
  have eq83621 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq51770 eq83614
    | (have j0 := eq83614 X0
       have j1 := eq51770 X0
       grind)
    | exact resolve eq83614 eq51770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51770 eq83614
  have eq83632 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq41789 eq83621
    | exact resolve eq83621 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83621
  have eq83639 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq31243 eq83632
    | (have j0 := eq83632 X0
       have j1 := eq31243 X0
       grind)
    | exact resolve eq83632 eq31243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31243 eq83632
  have eq83643 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq51803 eq83639
    | (have j0 := eq83639 X0
       have j1 := eq51803 X0
       grind)
    | exact resolve eq83639 eq51803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51803 eq83639
  have eq86777 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq32487 eq26
    | (have j1 := eq32487 (σ x)
       grind)
    | exact resolve eq26 eq32487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32487
  have eq86808 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq66419 eq86777
    | exact resolve eq86777 eq66419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66419 eq86777
  have eq86859 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41789 eq86808
    | exact resolve eq86808 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86808
  have eq86947 : (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq31525
    | exact resolve eq31525 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31525
  have eq86972 : (M.op (M.op x y) y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq693
    | exact resolve eq693 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86992 : (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq86947
  have eq87009 : (M.op (σ y) (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41789 eq86972
    | exact resolve eq86972 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86972
  have eq87019 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66602 eq86992
    | exact resolve eq86992 eq66602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66602 eq86992
  have eq87020 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq87019
  have eq87031 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq87009
    | exact resolve eq87009 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87009
  have eq87041 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87020 eq87031
    | exact resolve eq87031 eq87020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87031
  have eq87071 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq87020 eq38463
    | exact resolve eq38463 eq87020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38463 eq87020
  have eq87180 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq68486 eq87071
    | (have j1 := eq68486 (σ y)
       grind)
    | exact resolve eq87071 eq68486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68486 eq87071
  have eq87181 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq87180
  have eq87527 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq87041 eq28
    | (have j0 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq28 X0 (M.op x y)
       have r₂ := eq87041
       grind)
    | exact resolve eq28 eq87041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87041
  have eq87549 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq87527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87527
  have eq87601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87549 eq875
    | (have j0 := eq875 (M.op x y)
       grind)
    | exact resolve eq875 eq87549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq87549
  have eq87667 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq87601
  have eq87722 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq87667
    | exact resolve eq87667 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87667
  have eq87816 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq87181 eq857
    | (have j0 := eq857 (σ y) X0
       grind)
    | (have r₁ := eq857 (σ y) x
       have r₂ := eq87181
       grind)
    | exact resolve eq857 eq87181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857 eq87181
  have eq87834 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq87816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87816
  have eq88437 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87722 eq706
    | exact resolve eq706 eq87722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88454 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41789 eq88437
    | exact resolve eq88437 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88437
  have eq88471 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq88454
    | exact resolve eq88454 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86859 eq88454
  have eq89746 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88471 eq87722
    | exact resolve eq87722 eq88471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87722 eq88471
  have eq89774 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq89746
  have eq89799 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq89774 eq699
    | exact resolve eq699 eq89774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq89804 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq89774 eq728
    | exact resolve eq728 eq89774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89774
  have eq89930 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41789 eq89804
    | exact resolve eq89804 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89804
  have eq90042 : ∀ X0 : G, (σ y) ≠ (M.op (M.op x y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq89930 eq28
    | (have j0 := eq28 X0 (σ y)
       grind)
    | exact resolve eq28 eq89930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq90089 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq87834 eq90042
    | (have j0 := eq90042 X0
       have j1 := eq87834 X0
       grind)
    | exact resolve eq90042 eq87834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87834 eq90042
  have eq90099 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq90089 X0
       have j1 := eq83643 X0
       grind)
    | (have r₁ := eq90089 X0
       have r₂ := eq83643 X0
       grind)
    | exact resolve eq90089 eq83643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83643 eq90089
  have eq90130 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq90099 eq829
    | (have j0 := eq829 (σ y)
       grind)
    | (have r₁ := eq829 (σ y)
       have r₂ := eq90099 (σ y)
       grind)
    | exact resolve eq829 eq90099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90099
  have eq90225 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq90130
  have eq90393 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq90225 eq89930
    | exact resolve eq89930 eq90225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89930
  have eq90418 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq90393
  have eq95873 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq90225 eq89799
    | exact resolve eq89799 eq90225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89799 eq90225
  have eq96051 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq95873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95873
  have eq96513 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq96051 eq693
    | exact resolve eq693 eq96051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq96596 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq41789 eq96513
    | exact resolve eq96513 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96513
  have eq96634 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq90418 eq96596
    | exact resolve eq96596 eq90418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90418 eq96596
  have eq100234 : ∀ X0 : G, (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21213
       have i₂ := eq37669 (M.op sF0 y)
       grind)
    | exact superpose eq37669 eq21213
    | (have j1 := eq37669 X0
       grind)
    | exact resolve eq21213 eq37669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21213 eq37669
  have eq100325 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq32 eq100234
    | (have j0 := eq100234 X0
       grind)
    | exact resolve eq100234 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq100234
  have eq100571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq100325 eq829
    | (have j0 := eq829 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq829 (M.op (σ x) (σ y))
       have r₂ := eq100325 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq829 eq100325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100325
  have eq100635 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq100571
  have eq101965 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq100635 eq706
    | exact resolve eq706 eq100635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101980 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq100635 eq101965
    | exact resolve eq101965 eq100635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100635 eq101965
  have eq102150 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq101980 eq41590
    | exact resolve eq41590 eq101980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41590 eq101980
  have eq102183 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq102150
  have eq103961 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102183 eq728
    | exact resolve eq728 eq102183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq102183
  have eq104062 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq103961
    | exact resolve eq103961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103961
  have eq104073 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41551 eq104062
    | exact resolve eq104062 eq41551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41551 eq104062
  have eq104074 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by grind
  clear eq104073
  have eq104086 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq104074 eq27
    | exact resolve eq27 eq104074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104074
  have eq104252 : (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq104086
       have r₂ := eq41789
       grind)
    | exact resolve eq104086 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41789 eq104086
  have eq104259 : x = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq104252 eq30
    | exact resolve eq30 eq104252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq104252
  have eq104408 : y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41850 eq104259
    | exact resolve eq104259 eq41850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41850 eq104259
  have eq104468 : (M.op x y) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq18
    | exact resolve eq18 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104469 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq24
    | exact resolve eq24 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq104501 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq751 X0
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq751
    | exact resolve eq751 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104502 : ∀ X0 : G, (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq770 X0
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq770
    | exact resolve eq770 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq105471 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104468 eq30705
    | exact resolve eq30705 eq104468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30705
  have eq105483 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104468 eq96634
    | exact resolve eq96634 eq104468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96634
  have eq105512 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) := by grind
  clear eq105471
  have eq105535 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq104408 eq105512
    | exact resolve eq105512 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105512
  have eq105947 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105483 eq96051
    | exact resolve eq96051 eq105483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96051
  have eq105953 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105483 eq104469
    | exact resolve eq104469 eq105483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104469 eq105483
  have eq105959 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq105953
  have eq105963 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq105947 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105947
  have eq106056 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq105959
    | exact resolve eq105959 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105959
  have eq106057 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq106056
  have eq109141 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq105535 eq104502
    | exact resolve eq104502 eq105535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104502
  have eq109198 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq109141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109141
  have eq109360 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq109198 eq829
    | (have j0 := eq829 (M.op x y)
       grind)
    | (have r₁ := eq829 (M.op x y)
       have r₂ := eq109198 (M.op x y)
       grind)
    | exact resolve eq829 eq109198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109198
  have eq109433 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq109360
  have eq114694 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq105535 eq104501
    | exact resolve eq104501 eq105535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105535
  have eq114718 : ∀ X0 : G, (k (M.op x y) (σ y)) = (M.op (k (M.op x y) (σ y)) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq104501 X0
       have i₂ := eq11 sF0 sF3
       grind)
    | exact superpose eq11 eq104501
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq104501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114827 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104501 eq5522
    | exact resolve eq5522 eq104501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522
  have eq114879 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq114694 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114694
  have eq114889 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21157 eq114827
    | exact resolve eq114827 eq21157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21157 eq114827
  have eq114936 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq39284 eq114718
    | exact resolve eq114718 eq39284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39284 eq114718
  have eq114940 : (M.op (M.op x y) (σ y)) = (k (σ (M.op (M.op x y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24561 eq114889
    | exact resolve eq114889 eq24561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24561 eq114889
  have eq114965 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq114879 eq114936
    | (have j0 := eq114936 X0
       have j1 := eq114879 X0
       grind)
    | exact resolve eq114936 eq114879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114936
  have eq114966 : (M.op (M.op x y) (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109433 eq114940
    | exact resolve eq114940 eq109433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114940
  have eq114976 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq114879 eq114965
    | (have j0 := eq114965 X0
       have j1 := eq114879 X0
       grind)
    | exact resolve eq114965 eq114879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114879 eq114965
  have eq114977 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq114976 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114976
  have eq114978 : (M.op (M.op x y) (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109433 eq114966
    | exact resolve eq114966 eq109433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109433 eq114966
  have eq114980 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114977 eq114978
    | (have j1 := eq114977 (M.op x y)
       grind)
    | exact resolve eq114978 eq114977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114978
  have eq114981 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq114980
    | exact resolve eq114980 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114980
  have eq114982 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114977 eq114981
    | (have j1 := eq114977 (M.op x y)
       grind)
    | exact resolve eq114981 eq114977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114977 eq114981
  have eq114983 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq114982
  have eq114984 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105963 eq114983
    | (have j1 := eq105963 (M.op x y)
       grind)
    | exact resolve eq114983 eq105963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105963 eq114983
  have eq114985 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq114984
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq114984 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114984
  have eq114995 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114985 eq829
    | (have j0 := eq829 (M.op x y)
       grind)
    | (have r₁ := eq829 (M.op x y)
       have r₂ := eq114985
       grind)
    | exact resolve eq829 eq114985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq114985
  have eq115017 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq114995
  have eq115319 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115017 eq706
    | exact resolve eq706 eq115017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq115334 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104408 eq115319
    | exact resolve eq115319 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104408 eq115319
  have eq115351 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115017 eq115334
    | exact resolve eq115334 eq115017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115017 eq115334
  have eq115424 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq115351 eq104501
    | exact resolve eq104501 eq115351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104501 eq115351
  have eq115473 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq115424 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115424
  have eq115691 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115473 eq41051
    | exact resolve eq41051 eq115473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41051 eq115473
  have eq115853 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq115691
       have r₂ := eq77776
       grind)
    | exact resolve eq115691 eq77776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77776 eq115691
  have eq116646 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115853 eq27
    | exact resolve eq27 eq115853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115853
  have eq116843 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq116646
       have r₂ := eq106057
       grind)
    | exact resolve eq116646 eq106057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116646
  have eq116920 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104468
       have i₂ := eq116843
       grind)
    | exact superpose eq116843 eq104468
    | exact resolve eq104468 eq116843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104468
  have eq116928 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq116843
  have eq116932 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq116920
       have r₂ := eq116928
       grind)
    | exact resolve eq116920 eq116928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116920 eq116928
  have eq116967 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq116932
    | exact resolve eq116932 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116932
  have eq117049 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116967 eq27
    | exact resolve eq27 eq116967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116967
  have eq117185 : x = (M.op x y) := by
    first
    | (have r₁ := eq117049
       have r₂ := eq106057
       grind)
    | exact resolve eq117049 eq106057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106057 eq117049
  have eq117193 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq117185
       grind)
    | exact superpose eq117185 eq18
    | exact resolve eq18 eq117185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq117194 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq117185
       grind)
    | exact superpose eq117185 eq22
    | exact resolve eq22 eq117185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq117185
  have eq118408 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq117194 eq20
    | exact resolve eq20 eq117194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117194
  have eq119119 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq117193 eq751
    | exact resolve eq751 eq117193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq119134 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq117193 eq921
    | exact resolve eq921 eq117193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq119195 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq117193 eq21134
    | exact resolve eq21134 eq117193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21134 eq117193
  have eq119266 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq119195
    | exact resolve eq119195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119195
  have eq119326 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq119134
    | exact resolve eq119134 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq119134
  have eq119361 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq118408 eq119266
    | exact resolve eq119266 eq118408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119266
  have eq119409 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq118408 eq119326
    | exact resolve eq119326 eq118408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119326
  have eq119440 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq119361 eq119409
    | exact resolve eq119409 eq119361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119361 eq119409
  have eq119465 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq119440 eq26
    | exact resolve eq26 eq119440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq119631 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq119119 eq119465
    | exact resolve eq119465 eq119119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119119 eq119465
  have eq119878 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq119631 eq27
    | exact resolve eq27 eq119631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq119631
  have eq120008 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq118408 eq119878
    | exact resolve eq119878 eq118408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118408 eq119878
  have eq120015 : False := by grind
  exact eq120015

/-- `Equation4498`: `x ◇ (y ◇ y) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation4498 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4498 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4498.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq33 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq29
    | (have j0 := eq29 (M.op x y)
       grind)
    | exact resolve eq29 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
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
  have eq40 : y = (τ (σ y)) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) X3
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
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
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X1)
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) x
       have i₂ := eq9 (M.op x x) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq85 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) (τ X2))) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq15
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq15
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq208 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  have eq209 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq217 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X3) = (M.op (M.op X2 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X2 X3 (M.op X1 X1)
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = X2 ∨ (k X2 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 X1)
       have i₂ := eq9 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X2 X2) (M.op X2 X2))
       have r₂ := eq9 (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2) X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq50
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq263 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq33
       have i₂ := eq14 sF1 sF1
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq266 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq14 (σ X0) sF2
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq268 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ (k x x)) (σ x)
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq269 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq14 sF3 sF3
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 (σ (k y y)) (σ y)
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq274 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq273
  have eq275 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq268
  have eq276 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq263
  have eq280 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq269
    | exact resolve eq269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq311 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X1)
       have i₂ := eq57 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq9 X2 X3 (M.op X1 X1)
       have i₂ := eq57 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq333 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X4)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X2) X5) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 (M.op X2 X2) X5 X3 X4
       have i₂ := eq56 X0 X1 (M.op X2 X2) X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) X4) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 X4 (M.op X2 X2)
       have i₂ := eq56 X0 X1 (M.op X2 X2) X2
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq217 (M.op X1 X1) X2 X4 X3
       have i₂ := eq57 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq217 (M.op X1 X1) X2 X4 X3
       have i₂ := eq57 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq57 eq217
    | exact resolve eq217 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X1)) X4) = (M.op (M.op (M.op X2 X2) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq217 X2 X3 (M.op X1 X1) X4
       have i₂ := eq57 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq217 X2 X3 (M.op X1 X1) X4
       have i₂ := eq57 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq57 eq217
    | exact resolve eq217 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : (σ (k (k y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq274
       grind)
    | exact superpose eq274 eq36
    | exact resolve eq36 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq274
  have eq1019 : (σ (k (k y y) y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1016
  have eq1021 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq275
       grind)
    | exact superpose eq275 eq10
    | exact resolve eq10 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1093 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op X4 X4)) = (M.op X5 (M.op (M.op (M.op (M.op X0 X0) X1) X2) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X2 X2) X4 X5 X3
       have i₂ := eq56 X0 X1 (M.op X2 X2) X2
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op (M.op X4 X4) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 (M.op x x) X2 X4
       have i₂ := eq53 X1 X2 X0 x
       grind)
    | (have i₁ := eq9 X2 (M.op X0 X0) X2
       have i₂ := eq53 X0 (M.op X0 X0) X2 x
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1151 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X3 (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 X2 (M.op x x)
       have i₂ := eq53 X1 X2 X0 x
       grind)
    | (have i₁ := eq57 X0 (M.op X0 X0) X2
       have i₂ := eq53 X0 (M.op X0 X0) X2 X3
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X4)) = (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X5) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 (M.op X2 X2) X5 X3 X4
       have i₂ := eq53 X1 X2 X0 X2
       grind)
    | (have i₁ := eq56 (M.op (M.op X0 X0) X1) X1 X2 X3
       have i₂ := eq53 X0 X1 (M.op (M.op X0 X0) X1) X3
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X3 (M.op (M.op X2 X2) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op X1 X1)
       have i₂ := eq53 X0 X1 X2 X1
       grind)
    | (have i₁ := eq13 X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq53 X0 X1 (M.op (M.op X0 X0) X1) X3
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X3 (M.op (M.op X2 X2) X1)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1203 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X3 (M.op (M.op X2 X2) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1179 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1179 X0 X1 X2 X3
       have r₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact resolve eq1179 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1250 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) X2) = (M.op X4 (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 X3 X2 X4
       have i₂ := eq53 X1 X2 X0 X2
       grind)
    | (have i₁ := eq58 X0 (M.op X0 X0) X2
       have i₂ := eq53 X0 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) X3
       grind)
    | exact superpose eq53 eq58
    | exact resolve eq58 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1258 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) X2) = (M.op X4 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 X3 X2 X4
       have i₂ := eq56 X0 X1 (M.op X2 X2) X2
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1260 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58 X2 X1 X3
       have i₂ := eq57 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq58 X2 X1 X3
       have i₂ := eq57 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1313 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X0 X0) X1) = X2 ∨ (k X2 (M.op (M.op X1 X1) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq58 X0 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact superpose eq58 eq13
    | (have j0 := eq13 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1342 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = X2 ∨ (k X2 (M.op (M.op X1 X1) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1313 X0 X1 X2
       grind)
    | (have r₁ := eq1313 X2 X1 X2
       have r₂ := eq9 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq1313 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1552 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op X4 (M.op X1 X1)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1151 X2 (M.op x x) X1 X4
       have i₂ := eq311 (M.op x x) x X0 X1
       grind)
    | exact superpose eq311 eq1151
    | exact resolve eq1151 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op X4 (M.op X5 (M.op X2 X2))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq1260 X5 X2 x X4
       have i₂ := eq1260 X1 X2 x X0
       grind)
    | exact superpose eq1260 eq1260
    | exact resolve eq1260 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1842 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op (M.op (M.op X3 X3) X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq217 X3 X4 x X2
       have i₂ := eq1260 X1 X2 x X0
       grind)
    | exact superpose eq1260 eq217
    | exact resolve eq217 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1846 : ∀ X0 X1 X2 X3 X5 : G, (M.op X5 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq1151 X3 x X2 X5
       have i₂ := eq1260 X1 X2 x X0
       grind)
    | exact superpose eq1260 eq1151
    | exact resolve eq1151 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq1260
  have eq2720 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (k (τ (M.op X1 X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X1
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq209
    | exact resolve eq209 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2723 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 X1))) = (k (τ (M.op X1 X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X1
       have i₂ := eq57 X1 X1 X0
       grind)
    | (have i₁ := eq209 X1
       have i₂ := eq57 X0 X1 X1
       grind)
    | exact superpose eq57 eq209
    | exact resolve eq209 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq2880 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X1)) X2) ≠ (M.op (M.op X3 X3) (M.op X2 X2)) ∨ (M.op (M.op X3 X3) (M.op X2 X2)) = X4 ∨ (k X4 (M.op (M.op X0 (M.op X1 X1)) X2)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq234 X0 (M.op X3 X3) X2
       have i₂ := eq311 X0 X1 (M.op X3 X3) X3
       grind)
    | exact superpose eq311 eq234
    | (have j0 := eq234 X3 (M.op X2 X2) X4
       grind)
    | exact resolve eq234 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq2966 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = X4 ∨ (k X4 (M.op (M.op X0 (M.op X1 X1)) X2)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq2880 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq2880 X0 X1 X3 X3 X4
       have r₂ := eq311 X0 X1 (M.op X3 X3) X3
       grind)
    | exact resolve eq2880 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq2880
  have eq3040 : ∀ X0 X1 : G, (τ (M.op (M.op X1 X1) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2720 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2720
    | exact resolve eq2720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3045 : ∀ X0 X1 X2 : G, (σ (k X1 (k (τ (M.op X0 X0)) (τ X0)))) = (k (σ X1) (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op (M.op X2 X2) X0) X1
       have i₂ := eq2720 X2 X0
       grind)
    | exact superpose eq2720 eq49
    | exact resolve eq49 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3382 : ∀ X0 X1 X2 : G, (σ (k X1 (k (τ (M.op X0 X0)) (τ X0)))) = (k (σ X1) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X2 (M.op X0 X0)) X1
       have i₂ := eq2723 X2 X0
       grind)
    | exact superpose eq2723 eq49
    | exact resolve eq49 eq2723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3458 : ∀ X0 X1 X2 : G, (k (k (σ (τ (M.op X1 X1))) X1) X2) = (σ (k (τ (M.op (M.op X0 X0) X1)) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 (τ (M.op X1 X1)) X1 X2
       have i₂ := eq2720 X0 X1
       grind)
    | exact superpose eq2720 eq85
    | exact resolve eq85 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq3512 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 (k X0 (τ X1))
       have i₂ := eq85 X0 X1 X2
       grind)
    | exact superpose eq85 eq49
    | exact resolve eq49 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq3572 : ∀ X0 X1 X2 : G, (k (k (σ (τ (M.op X1 X1))) X1) X2) = (k (M.op (M.op X0 X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3458 X0 X1 X2
       have i₂ := eq50 (M.op (M.op X0 X0) X1) (τ X2)
       grind)
    | exact superpose eq50 eq3458
    | exact resolve eq3458 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458
  have eq3581 : ∀ X0 X1 X2 : G, (k (k (σ (τ (M.op X1 X1))) X1) X2) = (k (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3572 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq3572
    | exact resolve eq3572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3572
  have eq3582 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) X2) = (k (σ (k (τ (M.op X1 X1)) (τ X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3581 X0 X1 X2
       have i₂ := eq3512 (τ (M.op X1 X1)) X1 X2
       grind)
    | exact superpose eq3512 eq3581
    | exact resolve eq3581 eq3512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3512 eq3581
  have eq3583 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) X2) = (k (k (M.op X1 X1) (σ (τ X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3582 X0 X1 X2
       have i₂ := eq50 (M.op X1 X1) (τ X1)
       grind)
    | exact superpose eq50 eq3582
    | exact resolve eq3582 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3582
  have eq3584 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) X2) = (k (k (M.op X1 X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3583 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3583
    | exact resolve eq3583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583
  have eq3585 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) X2) = (k (M.op X1 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    grind
  clear eq3584
  have eq3967 : ∀ X0 X1 : G, (σ (k X0 (k (M.op x y) (τ X1)))) = (k (σ X0) (k (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq21 eq92
    | (have j0 := eq92 (M.op x y) X1 X0
       grind)
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq5128 : ∀ X0 X1 : G, (σ (k X0 (k (τ X1) (M.op x y)))) = (k (σ X0) (k X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq112
    | (have j0 := eq112 X1 (M.op x y) X0
       grind)
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq5548 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X1 X1) X0))) = (σ (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op (M.op X1 X1) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq257 (M.op X0 X0) (M.op (M.op X1 X1) X0)
       have i₂ := eq208 X1 X0
       grind)
    | exact superpose eq208 eq257
    | (have j0 := eq257 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq257 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq36087 : ∀ X0 X1 X5 : G, (k (M.op X1 (M.op X1 X1)) X5) = (k (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq3585 (M.op (M.op (M.op x x) x) x) X1 X5
       have i₂ := eq333 x x x X0 X1 (M.op (M.op (M.op x x) x) x)
       grind)
    | exact superpose eq333 eq3585
    | exact resolve eq3585 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq36242 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X2 X2) X1) X3) = (k (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3585 X2 X1 X3
       have i₂ := eq57 X1 X1 X0
       grind)
    | (have i₁ := eq3585 X2 X1 X3
       have i₂ := eq57 X0 X1 X1
       grind)
    | exact superpose eq57 eq3585
    | exact resolve eq3585 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585
  have eq38845 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X1 X1)) X2) = (k (M.op X3 (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36087 X3 X1 X2
       have i₂ := eq36087 X0 X1 X2
       grind)
    | (have i₁ := eq36087 X0 X1 x
       have i₂ := eq36087 X1 X1 x
       grind)
    | exact superpose eq36087 eq36087
    | exact resolve eq36087 eq36087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36087
  have eq39712 : ∀ X0 X1 X2 X3 : G, (σ (k (M.op X0 (M.op X1 X1)) (k (M.op x y) (τ X2)))) = (k (σ (M.op (M.op X3 X3) X1)) (k (σ (M.op x y)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3967 (M.op (M.op X2 X2) X1) X1
       have i₂ := eq36242 X0 X1 X2 (k sF0 (τ X1))
       grind)
    | exact superpose eq36242 eq3967
    | exact resolve eq3967 eq36242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39716 : ∀ X0 X1 X2 X3 : G, (σ (k X2 (k (τ (M.op (M.op X3 X3) X1)) (M.op x y)))) = (k (σ X2) (k (M.op X0 (M.op X1 X1)) (σ (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5128 X0 (M.op (M.op X2 X2) X1)
       have i₂ := eq36242 X0 X1 X2 sF1
       grind)
    | exact superpose eq36242 eq5128
    | exact resolve eq5128 eq36242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5128 eq36242
  have eq40762 : ∀ X0 X1 X2 X3 : G, (σ (k (M.op X0 (M.op X1 X1)) (k (M.op x y) (τ X2)))) = (k (σ (M.op X3 (M.op X1 X1))) (k (σ (M.op x y)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3967 (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq38845 X0 X1 (k sF0 (τ X1)) X3
       grind)
    | (have i₁ := eq3967 (M.op X3 (M.op X1 X1)) X1
       have i₂ := eq38845 X0 X1 (k sF0 (τ X1)) X3
       grind)
    | exact superpose eq38845 eq3967
    | exact resolve eq3967 eq38845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967 eq38845
  have eq40803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq280
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq280
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq280 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40803
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40803
    | exact resolve eq40803 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40803
  have eq40824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq40821
    | exact resolve eq40821 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40821
  have eq40825 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq40824
       have r₂ := eq28
       grind)
    | exact resolve eq40824 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40824
  have eq40826 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40825 eq1021
    | exact resolve eq1021 eq40825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq40943 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq40825
  have eq40948 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq40826
       have r₂ := eq40943
       grind)
    | exact resolve eq40826 eq40943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40826 eq40943
  have eq40951 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq40948
    | exact resolve eq40948 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40948
  have eq40956 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq40951
       grind)
    | exact superpose eq40951 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq40951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40951
  have eq40958 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq40956
  have eq41064 : ∀ X0 : G, (k (τ (σ x)) (τ (σ x))) = (τ (M.op X0 (σ x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq40958 eq2723
    | exact resolve eq2723 eq40958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41081 : ∀ X0 : G, (k x x) = (τ (M.op X0 (σ x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq39 eq41064
    | exact resolve eq41064 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41064
  have eq52606 : ∀ X0 X2 X3 : G, (k X0 (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X0) ∨ (k X0 (M.op (M.op X3 X3) X2)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq208 X0 (M.op x x)
       have i₂ := eq1203 X0 x X2 X3
       grind)
    | (have i₁ := eq208 X0 x
       have i₂ := eq1203 X0 x X2 (M.op (M.op X0 X0) x)
       grind)
    | exact superpose eq1203 eq208
    | (have j1 := eq1203 X0 X2 X3 X0
       grind)
    | exact resolve eq208 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq1203
  have eq56877 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40958 eq41081
    | exact resolve eq41081 eq40958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40958 eq41081
  have eq56927 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq56877
  have eq56947 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39 eq56927
    | exact resolve eq56927 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56927
  have eq57015 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq56947
       grind)
    | exact superpose eq56947 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq56947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56947
  have eq57017 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq57015
  have eq57035 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  have eq57040 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 x
       have i₂ := eq57017
       grind)
    | exact superpose eq57017 eq54
    | exact resolve eq54 eq57017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57043 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 x x
       have i₂ := eq57017
       grind)
    | exact superpose eq57017 eq57
    | exact resolve eq57 eq57017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57097 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X0 (M.op y X1)) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1148 X0 x X1 X2
       have i₂ := eq57017
       grind)
    | exact superpose eq57017 eq1148
    | exact resolve eq1148 eq57017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq57130 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 y)) = (M.op X2 y) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1552 X0 x X2 x
       have i₂ := eq57017
       grind)
    | exact superpose eq57017 eq1552
    | exact resolve eq1552 eq57017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57142 : ∀ X0 : G, (k (τ y) (τ x)) = (τ (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2723 X0 x
       have i₂ := eq57017
       grind)
    | exact superpose eq57017 eq2723
    | exact resolve eq2723 eq57017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57017
  have eq57160 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq57035
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57035
    | exact resolve eq57035 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57035
  have eq57162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq280
       have i₂ := eq57160
       grind)
    | exact superpose eq57160 eq280
    | exact resolve eq280 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq57166 : (τ (M.op x y)) = (k (τ y) (τ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129 y x
       have i₂ := eq57160
       grind)
    | exact superpose eq57160 eq129
    | exact resolve eq129 eq57160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57160
  have eq57170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq57162
    | exact resolve eq57162 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57162
  have eq57172 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq57170
       have r₂ := eq28
       grind)
    | exact resolve eq57170 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57170
  have eq57769 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq57043 x X0
       grind)
    | (have i₁ := eq19
       have i₂ := eq57043 X0 x
       grind)
    | exact superpose eq57043 eq19
    | (have j1 := eq57043 x X0
       grind)
    | exact resolve eq19 eq57043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57043
  have eq58237 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1161 x x x X0 y x
       have i₂ := eq57769 (M.op (M.op x (M.op (M.op x x) x)) x)
       grind)
    | exact superpose eq57769 eq1161
    | exact resolve eq1161 eq57769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58249 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) ∨ (M.op x y) = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 X1 x
       have i₂ := eq57769 X2
       grind)
    | exact superpose eq57769 eq54
    | (have j1 := eq57769 X2
       grind)
    | exact resolve eq54 eq57769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58922 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) X2) = (M.op X3 (M.op X4 X0)) ∨ (k X0 (M.op (M.op X2 X2) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1250 X4 x X2 X1 X3
       have i₂ := eq1342 x X2 X0
       grind)
    | (have i₁ := eq1250 X0 X1 X2 X3 X4
       have i₂ := eq1342 X0 X1 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq1342 eq1250
    | (have j1 := eq1342 X1 X2 (M.op X3 (M.op X4 X0))
       grind)
    | exact resolve eq1250 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq1342
  have eq61311 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq58237 X0
       have i₂ := eq57769 y
       grind)
    | exact superpose eq57769 eq58237
    | exact resolve eq58237 eq57769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57769 eq58237
  have eq61695 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq61311 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61311
  have eq66121 : ∀ X0 : G, (k (M.op x y) (σ X0)) = (σ (k (k (τ y) (τ x)) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq57166 eq50
    | exact resolve eq50 eq57166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57166
  have eq66152 : ∀ X0 : G, (k (M.op x y) (σ X0)) = (k (k y (σ (τ x))) (σ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq66121 X0
       have i₂ := eq111 y (τ x) X0
       grind)
    | exact superpose eq111 eq66121
    | exact resolve eq66121 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq66121
  have eq66156 : ∀ X0 : G, (k (M.op x y) (σ X0)) = (k (k y x) (σ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq66152 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq66152
    | exact resolve eq66152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66152
  have eq76719 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq61695 eq57040
    | exact resolve eq57040 eq61695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57040 eq61695
  have eq77537 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq76719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76719
  have eq100175 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | (have j0 := eq58249 X0 y (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58249
  have eq100176 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | (have j0 := eq100175 X0
       grind)
    | (have r₁ := eq100175 X0
       have r₂ := eq19
       grind)
    | exact resolve eq100175 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100175
  have eq100655 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x y) X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq363 x y X3 X0 X1
       have i₂ := eq100176 x
       grind)
    | exact superpose eq100176 eq363
    | exact resolve eq363 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq100660 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq747 X0 X1 x y X2
       have i₂ := eq100176 x
       grind)
    | exact superpose eq100176 eq747
    | exact resolve eq747 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq100680 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1258 x y X1 X0 X2
       have i₂ := eq100176 x
       grind)
    | exact superpose eq100176 eq1258
    | exact resolve eq1258 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq100687 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1842 X0 X1 X2 x y
       have i₂ := eq100176 x
       grind)
    | exact superpose eq100176 eq1842
    | exact resolve eq1842 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq100729 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq719 (M.op x x) x y X1 X0
       have i₂ := eq100176 (M.op x x)
       grind)
    | exact superpose eq100176 eq719
    | exact resolve eq719 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq100740 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op y y)) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1093 x x (M.op (M.op x x) x) X0 y X1
       have i₂ := eq100176 (M.op (M.op x x) x)
       grind)
    | exact superpose eq100176 eq1093
    | exact resolve eq1093 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq100746 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1161 (M.op (M.op x x) x) x x X0 X1 y
       have i₂ := eq100176 (M.op (M.op x x) x)
       grind)
    | exact superpose eq100176 eq1161
    | exact resolve eq1161 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100750 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq1161 x x x X0 y (M.op x (M.op (M.op x x) x))
       have i₂ := eq100176 (M.op x (M.op (M.op x x) x))
       grind)
    | exact superpose eq100176 eq1161
    | exact resolve eq1161 eq100176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq100176
  have eq101531 : ∀ X0 X2 X3 : G, (k X0 (M.op (M.op x y) X2)) = (M.op (M.op (M.op x y) X2) X0) ∨ (k X0 (M.op (M.op X3 X3) X2)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq52606 X0 x X3
       have i₂ := eq100746 (M.op x x) x
       grind)
    | exact superpose eq100746 eq52606
    | (have j0 := eq52606 X0 X2 X3
       grind)
    | exact resolve eq52606 eq100746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52606
  have eq101548 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op (M.op x y) X2)) = X0 ∨ (M.op (M.op X1 X1) X2) = (M.op X3 (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58922 X0 X1 X2 X3 X4
       have i₂ := eq100746 (M.op X2 X2) X2
       grind)
    | exact superpose eq100746 eq58922
    | (have j0 := eq58922 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq58922 eq100746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58922
  have eq101681 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x y) X2) = X4 ∨ (k X4 (M.op (M.op X0 (M.op X1 X1)) X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2966 X0 X1 X2 x X4
       have i₂ := eq100746 (M.op x x) X2
       grind)
    | exact superpose eq100746 eq2966
    | (have j0 := eq2966 X0 X1 X2 x X4
       grind)
    | exact resolve eq2966 eq100746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2966
  have eq102406 : (σ (k (k y y) y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1019
       have i₂ := eq100746 sF3 sF3
       grind)
    | exact superpose eq100746 eq1019
    | exact resolve eq1019 eq100746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq102407 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq100740 x X1
       have i₂ := eq100750 (M.op x x)
       grind)
    | exact superpose eq100750 eq100740
    | exact resolve eq100740 eq100750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100740 eq100750
  have eq102628 : ∀ X0 X1 : G, (σ (k X1 (k (τ (M.op X0 X0)) (τ X0)))) = (k (σ X1) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3045 X0 X1 x
       have i₂ := eq100729 x X0
       grind)
    | exact superpose eq100729 eq3045
    | exact resolve eq3045 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq102689 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op x y) X0))) = (σ (M.op (M.op X0 X0) (M.op (M.op x y) X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op (M.op X1 X1) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5548 X1 X0
       have i₂ := eq100729 X0 X1
       grind)
    | exact superpose eq100729 eq5548
    | (have j0 := eq5548 X0 X1
       grind)
    | exact resolve eq5548 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5548
  have eq103841 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 (M.op X1 X1)) (k (M.op x y) (τ X2)))) = (k (σ (M.op (M.op x y) X1)) (k (σ (M.op x y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39712 X0 X1 X2 x
       have i₂ := eq100729 x X1
       grind)
    | exact superpose eq100729 eq39712
    | exact resolve eq39712 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39712
  have eq103845 : ∀ X0 X1 X2 : G, (k (σ X2) (k (M.op X0 (M.op X1 X1)) (σ (M.op x y)))) = (σ (k X2 (k (τ (M.op (M.op x y) X1)) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39716 X0 X1 X2 x
       have i₂ := eq100729 x X1
       grind)
    | exact superpose eq100729 eq39716
    | exact resolve eq39716 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39716
  have eq104743 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) X1) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq57097 X0 X1 x
       have i₂ := eq100729 x X1
       grind)
    | exact superpose eq100729 eq57097
    | exact resolve eq57097 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57097
  have eq105750 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X1 X1)) = (M.op (M.op x y) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 X1
       have i₂ := eq100729 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq100729 eq313
    | exact resolve eq313 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq106046 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op x y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3040 X0 x
       have i₂ := eq100729 x (σ X0)
       grind)
    | exact superpose eq100729 eq3040
    | exact resolve eq3040 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq106408 : ∀ X1 X2 : G, (M.op (M.op x y) X1) = (M.op X2 (M.op (M.op x y) X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq100680 x X1 X2
       have i₂ := eq100729 x X1
       grind)
    | exact superpose eq100729 eq100680
    | exact resolve eq100680 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100680
  have eq107035 : ∀ X1 X3 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X3) X1) := by
    intro X1 X3
    first
    | (have i₁ := eq100655 x X1 X3
       have i₂ := eq100729 x X1
       grind)
    | exact superpose eq100729 eq100655
    | exact resolve eq100655 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100655
  have eq107547 : ∀ X2 X4 : G, (k X4 (M.op (M.op x y) X2)) = X4 ∨ (M.op (M.op x y) X2) = X4 := by
    intro X2 X4
    first
    | (have i₁ := eq101681 x x X2 X4
       have i₂ := eq100660 x x X2
       grind)
    | exact superpose eq100660 eq101681
    | (have j0 := eq101681 x x X2 X4
       grind)
    | exact resolve eq101681 eq100660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100660 eq101681
  have eq107637 : ∀ X0 X2 X3 X4 : G, (M.op (M.op x y) X2) = (M.op X3 (M.op X4 X0)) ∨ (k X0 (M.op (M.op x y) X2)) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq101548 X0 x X2 X3 X4
       have i₂ := eq100729 x X2
       grind)
    | exact superpose eq100729 eq101548
    | (have j0 := eq101548 X0 x X2 X3 X4
       grind)
    | exact resolve eq101548 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101548
  have eq107651 : ∀ X0 X2 : G, (k X0 (M.op (M.op x y) X2)) = X0 ∨ (k X0 (M.op (M.op x y) X2)) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq101531 X0 X2 x
       have i₂ := eq100729 x X2
       grind)
    | exact superpose eq100729 eq101531
    | (have j0 := eq101531 X0 X2 x
       grind)
    | exact resolve eq101531 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101531
  have eq108746 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X1 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105750 X1 x
       have i₂ := eq100687 sF0 X1 x
       grind)
    | exact superpose eq100687 eq105750
    | exact resolve eq105750 eq100687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100687 eq105750
  have eq110114 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op x y) X0))) = (σ (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op (M.op X1 X1) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq102689 X0 X1
       have i₂ := eq100729 X0 (M.op sF0 X0)
       grind)
    | exact superpose eq100729 eq102689
    | (have j0 := eq102689 X0 X1
       grind)
    | exact resolve eq102689 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102689
  have eq111788 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (k X0 (M.op (M.op x y) X2)) ∨ (k X0 (M.op (M.op x y) X2)) = X0 := by
    intro X0 X2
    first
    | exact superpose eq107035 eq107651
    | (have j0 := eq107651 X0 X2
       grind)
    | exact resolve eq107651 eq107035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107651
  have eq113307 : ∀ X0 X1 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op x y) X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op (M.op X1 X1) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq106408 eq110114
    | (have j0 := eq110114 X0 X1
       grind)
    | exact resolve eq110114 eq106408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110114
  have eq115305 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op x y) X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq113307 X0 x
       have i₂ := eq100729 x X0
       grind)
    | exact superpose eq100729 eq113307
    | (have j0 := eq113307 X0 x
       grind)
    | exact resolve eq113307 eq100729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113307
  have eq117901 : ∀ X0 : G, (k (τ (M.op x y)) (τ (M.op x y))) = (τ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq102407 eq2723
    | exact resolve eq2723 eq102407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117907 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq102407 eq108746
    | exact resolve eq108746 eq102407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108746
  have eq117920 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq102407 eq117907
    | exact resolve eq117907 eq102407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117907
  have eq117925 : (τ (M.op x y)) = (k (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | exact superpose eq102407 eq117901
    | exact resolve eq117901 eq102407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117901
  have eq117933 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq117920 eq276
    | exact resolve eq276 eq117920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq117991 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq117933
    | exact resolve eq117933 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117933
  have eq117992 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq117991
  have eq118025 : ∀ X0 : G, (k (τ (σ (M.op x y))) (τ (σ (M.op x y)))) = (τ (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq117992 eq2723
    | exact resolve eq2723 eq117992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723 eq117992
  have eq118034 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq38 eq118025
    | exact resolve eq118025 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118025
  have eq118036 : ∀ X0 : G, (M.op x y) = (τ (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq117920 eq118034
    | exact resolve eq118034 eq117920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117920 eq118034
  have eq118051 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq118036 eq11
    | exact resolve eq11 eq118036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118036
  have eq118097 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq118051
    | (have j0 := eq118051 X0
       grind)
    | exact resolve eq118051 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118051
  have eq118653 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | exact superpose eq117925 eq14
    | (have j0 := eq14 (τ (M.op x y)) (τ (M.op x y))
       grind)
    | exact resolve eq14 eq117925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117925
  have eq118655 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq118653
  have eq119150 : ∀ X0 : G, (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = X0 ∨ (k X0 (τ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq118655 eq13
    | (have j0 := eq13 X0 (τ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (τ (M.op x y))
       have r₂ := eq118655
       grind)
    | exact resolve eq13 eq118655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119165 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ (τ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq119150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119150
  have eq119303 : ∀ X0 : G, (M.op (τ (M.op x y)) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq118655 eq100729
    | exact resolve eq100729 eq118655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119499 : (τ (M.op x y)) = (M.op (M.op x y) (τ (M.op x y))) := by
    first
    | exact superpose eq119303 eq118655
    | exact resolve eq118655 eq119303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118655 eq119303
  have eq120348 : ∀ X0 : G, (τ (M.op x y)) = (M.op X0 (τ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq119499 eq106408
    | exact resolve eq106408 eq119499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119499
  have eq121092 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) X0))) (σ (M.op (M.op x y) (M.op (M.op x y) X0)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) X0))) (σ (M.op (M.op x y) (M.op (M.op x y) X0)))) ∨ (σ (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) X0))) (σ (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | exact superpose eq107035 eq115305
    | exact resolve eq115305 eq107035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115305
  have eq121200 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op (σ (M.op (M.op x y) (M.op (M.op x y) X0))) (σ (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have j0 := eq121092 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121092
  have eq121231 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq106408 eq121200
    | exact resolve eq121200 eq106408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121200
  have eq121530 : (M.op (σ x) (σ (M.op x x))) = (σ (M.op x (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq266
  have eq123074 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op x y)))) ∨ (τ X0) = (τ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq119165 eq50
    | (have j1 := eq119165 (τ X0)
       grind)
    | exact resolve eq50 eq119165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119165
  have eq123085 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op x y)) ∨ (τ X0) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq123074 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq123074
    | (have j0 := eq123074 X0
       grind)
    | exact resolve eq123074 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123074
  have eq123101 : ∀ X0 : G, (τ X0) = (τ (M.op x y)) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq123085 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq123085
    | (have j0 := eq123085 X0
       grind)
    | exact resolve eq123085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123085
  have eq123178 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120348 X0
       have i₂ := eq123101 sF0
       grind)
    | (have i₁ := eq120348 X0
       have i₂ := eq123101 (τ sF0)
       grind)
    | exact superpose eq123101 eq120348
    | (have j1 := eq123101 X0
       grind)
    | exact resolve eq120348 eq123101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123101
  have eq123473 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq38 eq255
    | (have j0 := eq255 X0 x
       grind)
    | exact resolve eq255 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123475 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = X0 ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq40 eq255
    | (have j0 := eq255 X0 x
       grind)
    | exact resolve eq255 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123505 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ (σ X0))) X2)) = (k (σ (M.op X0 (τ (σ X1)))) (σ X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 X1 (σ X0) X2
       have i₂ := eq255 X0 (σ X1)
       grind)
    | exact superpose eq255 eq91
    | (have j1 := eq255 X0 (σ X1)
       grind)
    | exact resolve eq91 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq255
  have eq123598 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ (σ X0))) X2)) = (σ (k (M.op X0 (τ (σ X1))) X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123505 X0 X1 X2
       have i₂ := eq15 (M.op X0 (τ (σ X1))) X2
       grind)
    | exact superpose eq15 eq123505
    | (have j0 := eq123505 X0 X1 X2
       grind)
    | exact resolve eq123505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123505
  have eq123618 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = X0 ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq37 eq123475
    | (have j0 := eq123475 X0
       grind)
    | exact resolve eq123475 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq123475
  have eq123620 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq102407 eq123473
    | (have j0 := eq123473 X0
       grind)
    | exact resolve eq123473 eq102407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123473
  have eq123663 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ (σ X0))) X2)) = (σ (k (M.op X0 X1) X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123598 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq123598
    | (have j0 := eq123598 X0 X1 X2
       grind)
    | exact resolve eq123598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123598
  have eq123681 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op x y) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq29 eq123620
    | (have j0 := eq123620 X0
       grind)
    | exact resolve eq123620 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123620
  have eq123715 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (σ (k (M.op X0 X1) X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123663 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123663
    | (have j0 := eq123663 X0 X1 X2
       grind)
    | exact resolve eq123663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123663
  have eq123724 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op x y) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq21 eq123681
    | (have j0 := eq123681 X0
       grind)
    | exact resolve eq123681 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123681
  have eq123740 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (σ (k (M.op X0 X1) X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123715 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq123715
    | (have j0 := eq123715 X0 X1 X2
       grind)
    | exact resolve eq123715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123715
  have eq165510 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ X0 ∨ (k X0 (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq111788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111788
  have eq166845 : ∀ X0 : G, (k (M.op x y) X0) = (τ (σ (M.op x y))) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq123724 eq10
    | (have j1 := eq123724 X0
       grind)
    | exact resolve eq10 eq123724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123724
  have eq166922 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq38 eq166845
    | (have j0 := eq166845 X0
       grind)
    | exact resolve eq166845 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166845
  have eq166973 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq166922 X0
       have j1 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq166922 x
       have r₂ := eq13 X0 x
       grind)
    | (have r₁ := eq166922 (M.op x y)
       have r₂ := eq13 X0 (M.op x y)
       grind)
    | exact resolve eq166922 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166922
  have eq167002 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (M.op x y) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq166973 eq49
    | (have j1 := eq166973 (τ X0)
       grind)
    | exact resolve eq49 eq166973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166973
  have eq167101 : ∀ X0 : G, (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21 eq167002
    | (have j0 := eq167002 X0
       grind)
    | exact resolve eq167002 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167002
  have eq173853 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ X1 ∨ (k X1 (M.op (M.op x y) X2)) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq100746 eq165510
    | (have j0 := eq165510 X1 X2
       grind)
    | (have r₁ := eq165510 (M.op (M.op x y) (M.op x y)) X1
       have r₂ := eq100746 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq165510 eq100746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173900 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq106408 eq165510
    | (have j0 := eq165510 (M.op (M.op x y) X0) X1
       grind)
    | (have r₁ := eq165510 (M.op (M.op x y) X1) X1
       have r₂ := eq106408 X1 (M.op x y)
       grind)
    | exact resolve eq165510 eq106408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165510
  have eq173960 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq173900 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173900
  have eq183452 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) X3) = (k (M.op (M.op x y) X3) (M.op X0 (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq173960 X0 (M.op X1 (M.op X2 X2))
       have i₂ := eq1751 sF0 X1 X2 x x
       grind)
    | (have i₁ := eq173960 X0 (M.op x (M.op X2 X2))
       have i₂ := eq1751 X0 X1 X2 sF0 x
       grind)
    | exact superpose eq1751 eq173960
    | exact resolve eq173960 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq183473 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (τ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq120348 eq173960
    | exact resolve eq173960 eq120348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120348
  have eq183502 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq118097 eq173960
    | exact resolve eq173960 eq118097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118097 eq173960
  have eq183612 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq183502 (M.op X0 (M.op X1 (M.op x x)))
       have i₂ := eq1846 X0 X1 x sF0 x
       grind)
    | exact superpose eq1846 eq183502
    | exact resolve eq183502 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq183678 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (k (τ (M.op (M.op x y) X0)) (τ (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq183502 eq129
    | exact resolve eq129 eq183502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq183502
  have eq183698 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (k (τ (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq38 eq183678
    | exact resolve eq183678 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183678
  have eq183707 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ (M.op (M.op x y) X1)) (M.op x y)))) = (k (σ X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq183612 eq103845
    | exact resolve eq103845 eq183612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103845 eq183612
  have eq183725 : ∀ X0 X1 X2 : G, (σ (k X2 (τ (M.op (M.op x y) X1)))) = (k (σ X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq183698 eq183707
    | exact resolve eq183707 eq183698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183698 eq183707
  have eq183996 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (k (σ (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq183473 eq49
    | exact resolve eq49 eq183473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183473
  have eq188588 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq183996 (τ X0)
       have i₂ := eq123178 X0 sF0
       grind)
    | exact superpose eq123178 eq183996
    | (have j1 := eq123178 (σ (τ X0)) x
       grind)
    | exact resolve eq183996 eq123178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123178 eq183996
  have eq188707 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq188588 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188588
    | (have j0 := eq188588 X0
       grind)
    | exact resolve eq188588 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188588
  have eq188708 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq188707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188707
  have eq191562 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq188708 eq50
    | exact resolve eq50 eq188708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188708
  have eq191585 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq191562
    | (have j0 := eq191562 X0
       grind)
    | exact resolve eq191562 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191562
  have eq191752 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq191585 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191585
    | exact resolve eq191585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191585
  have eq198474 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (M.op (τ X0) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    grind
  clear eq167101
  have eq198566 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ X0)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq102407 eq198474
    | (have j0 := eq198474 X0
       grind)
    | exact resolve eq198474 eq102407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102407 eq198474
  have eq198619 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq198566 eq49
    | (have j1 := eq198566 X0
       grind)
    | exact resolve eq49 eq198566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198566
  have eq198686 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21 eq198619
    | (have j0 := eq198619 X0
       grind)
    | exact resolve eq198619 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198619
  have eq198687 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq198686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198686
  have eq198786 : ∀ X0 X1 X2 X3 : G, (σ (k (M.op X0 (M.op X1 X1)) (k (M.op x y) (τ X2)))) = (k (σ (M.op X3 (M.op X1 X1))) (σ (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq198687 eq40762
    | exact resolve eq40762 eq198687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40762
  have eq198787 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 (M.op X1 X1)) (k (M.op x y) (τ X2)))) = (k (σ (M.op (M.op x y) X1)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq198687 eq103841
    | exact resolve eq103841 eq198687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103841
  have eq199163 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq198687 eq29
    | exact resolve eq29 eq198687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq198687
  have eq199689 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 (M.op X1 X1)) (k (M.op x y) (τ X2)))) = (σ (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq191752 eq198787
    | exact resolve eq198787 eq191752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198787
  have eq199690 : ∀ X0 X1 X2 X3 : G, (σ (k (M.op X0 (M.op X1 X1)) (k (M.op x y) (τ X2)))) = (σ (M.op X3 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq191752 eq198786
    | exact resolve eq198786 eq191752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198786
  have eq199820 : ∀ X1 X3 : G, (σ (M.op X3 (M.op X1 X1))) = (σ (M.op (M.op x y) X1)) := by
    intro X1 X3
    first
    | exact superpose eq199689 eq199690
    | exact resolve eq199690 eq199689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199689 eq199690
  have eq200252 : ∀ X0 : G, (k (M.op x y) X0) = (τ (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq199163 eq10
    | exact resolve eq10 eq199163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199163
  have eq200342 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq38 eq200252
    | exact resolve eq200252 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq200252
  have eq200461 : ∀ X0 : G, (M.op x y) = (k (k y x) (σ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq200342 eq66156
    | exact resolve eq66156 eq200342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66156 eq200342
  have eq202458 : ∀ X0 X1 X2 : G, (σ (M.op (M.op x y) X2)) = (σ (M.op X0 (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199820 X2 x
       have i₂ := eq1552 X1 X2 X0 x
       grind)
    | exact superpose eq1552 eq199820
    | exact resolve eq199820 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq210272 : ∀ X0 : G, (M.op x y) = (k (k y x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq200461 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200461
    | exact resolve eq200461 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200461
  have eq211611 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (k y x)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq49 X0 (k y x)
       have i₂ := eq210272 (τ X0)
       grind)
    | exact superpose eq210272 eq49
    | exact resolve eq49 eq210272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq210272
  have eq211732 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (k y x)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21 eq211611
    | (have j0 := eq211611 X0
       grind)
    | exact resolve eq211611 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211611
  have eq217728 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq191752 (σ (k y x))
       have i₂ := eq211732 sF1
       grind)
    | exact superpose eq211732 eq191752
    | exact resolve eq191752 eq211732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191752
  have eq229138 : ∀ X0 X1 X2 : G, (τ (M.op (M.op x y) (σ (M.op (M.op x y) X0)))) = (k (τ (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0)))) (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106046 (M.op X0 (M.op X1 (M.op X2 X2)))
       have i₂ := eq202458 X0 X1 X2
       grind)
    | exact superpose eq202458 eq106046
    | exact resolve eq106046 eq202458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106046 eq202458
  have eq229558 : ∀ X0 X1 X2 : G, (τ (M.op (M.op x y) (σ (M.op (M.op x y) X0)))) = (k (τ (σ (M.op (M.op x y) X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq121231 eq229138
    | exact resolve eq229138 eq121231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121231 eq229138
  have eq229666 : ∀ X0 X1 X2 : G, (k (M.op (M.op x y) X0) (M.op X1 (M.op X2 (M.op X0 X0)))) = (τ (M.op (M.op x y) (σ (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq229558 X0 X1 X2
       have i₂ := eq10 (M.op sF0 X0)
       grind)
    | exact superpose eq10 eq229558
    | exact resolve eq229558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229558
  have eq229752 : ∀ X0 : G, (M.op (M.op x y) X0) = (τ (M.op (M.op x y) (σ (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | exact superpose eq183452 eq229666
    | exact resolve eq229666 eq183452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183452 eq229666
  have eq229967 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (M.op x y) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq229752 eq11
    | exact resolve eq11 eq229752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229752
  have eq230357 : ∀ X0 X1 : G, (σ (M.op (M.op x y) X0)) = (M.op X1 (σ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq229967 eq106408
    | exact resolve eq106408 eq229967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229967
  have eq309208 : ∀ X0 X2 X3 : G, (M.op (M.op x y) X0) ≠ X2 ∨ (k X2 (M.op (M.op x y) X3)) = X2 ∨ (k X2 (M.op (M.op x y) X0)) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq173853 x X2 X3
       have i₂ := eq107637 X2 X0 x X2
       grind)
    | (have i₁ := eq173853 (M.op x y) x X2
       have i₂ := eq107637 X0 (M.op x x) X3 x
       grind)
    | exact superpose eq107637 eq173853
    | (have j0 := eq173853 X0 X2 X3
       have j1 := eq107637 X2 X3 X3 x
       grind)
    | (have r₁ := eq173853 (M.op x y) (M.op X3 (M.op x X0)) X2
       have r₂ := eq107637 X0 (M.op (M.op X3 (M.op x X0)) (M.op X3 (M.op x X0))) X3 x
       grind)
    | (have r₁ := eq173853 X3 (M.op (M.op x y) X2) X2
       have r₂ := eq107637 (M.op (M.op x y) X2) X2 X3 (M.op (M.op x y) X2)
       grind)
    | exact resolve eq173853 eq107637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107637 eq173853
  have eq309301 : ∀ X0 X2 X3 : G, (k X2 (M.op (M.op x y) X3)) = X2 ∨ (k X2 (M.op (M.op x y) X0)) = X2 := by
    intro X0 X2 X3
    first
    | (have j0 := eq309208 X3 X2 X3
       have j1 := eq107547 X3 X2
       grind)
    | (have r₁ := eq309208 X0 (k (M.op (M.op x y) X0) (M.op (M.op x y) X2)) X3
       have r₂ := eq107547 X2 (M.op (M.op x y) X0)
       grind)
    | (have r₁ := eq309208 X2 x X3
       have r₂ := eq107547 X2 x
       grind)
    | (have r₁ := eq309208 X0 (M.op (M.op x y) X2) X3
       have r₂ := eq107547 X2 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq309208 eq107547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107547 eq309208
  have eq327754 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq309301 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309301
  have eq327755 : ∀ X0 X1 : G, (k X0 (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq327754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327754
  have eq328100 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 (k (τ (M.op X0 X0)) (τ X0)))) := by
    intro X0 X1
    first
    | exact superpose eq327755 eq102628
    | exact resolve eq102628 eq327755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102628 eq327755
  have eq329947 : ∀ X0 X1 X2 : G, (σ X1) = (k (σ X1) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3382 X0 X1 X2
       have i₂ := eq328100 X0 X1
       grind)
    | exact superpose eq328100 eq3382
    | exact resolve eq3382 eq328100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382 eq328100
  have eq330323 : ∀ X1 X2 : G, (σ X2) = (σ (k X2 (τ (M.op (M.op x y) X1)))) := by
    intro X1 X2
    first
    | (have i₁ := eq183725 x X1 X2
       have i₂ := eq329947 X1 X2 x
       grind)
    | exact superpose eq329947 eq183725
    | exact resolve eq183725 eq329947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183725 eq329947
  have eq334259 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq330323 eq10
    | exact resolve eq10 eq330323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330323
  have eq334417 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op x y) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq334259 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq334259
    | exact resolve eq334259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334259
  have eq335034 : ∀ X0 : G, (M.op (τ (M.op (M.op x y) X0)) (τ (M.op (M.op x y) X0))) = (M.op (τ (M.op (M.op x y) X0)) (M.op (τ (M.op (M.op x y) X0)) (τ (M.op (M.op x y) X0)))) := by
    intro X0
    grind
  have eq335245 : ∀ X0 : G, (M.op (τ (M.op (M.op x y) X0)) (τ (M.op (M.op x y) X0))) = (M.op (M.op x y) (τ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq335034 X0
       have i₂ := eq100746 (τ (M.op sF0 X0)) (τ (M.op sF0 X0))
       grind)
    | exact superpose eq100746 eq335034
    | exact resolve eq335034 eq100746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335034
  have eq408346 : ∀ X0 : G, (M.op X0 y) = (σ (k (τ y) (τ x))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 y)
       have i₂ := eq57142 X0
       grind)
    | exact superpose eq57142 eq11
    | exact resolve eq11 eq57142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57142
  have eq408398 : ∀ X0 : G, (M.op X0 y) = (k y (σ (τ x))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq408346 X0
       have i₂ := eq50 y (τ x)
       grind)
    | exact superpose eq50 eq408346
    | exact resolve eq408346 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq408346
  have eq408420 : ∀ X0 : G, (k y x) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq408398 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq408398
    | exact resolve eq408398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408398
  have eq408592 : ∀ X0 X1 : G, (k y x) = (M.op X0 (M.op X1 y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq57130 X0 X1 x
       have i₂ := eq408420 x
       grind)
    | exact superpose eq408420 eq57130
    | exact resolve eq57130 eq408420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57130 eq408420
  have eq408844 : ∀ X0 X1 : G, (k y x) = (M.op X0 (M.op X1 y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq408592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408592
  have eq414835 : ∀ X1 : G, (k y x) = (M.op X1 (k y x)) ∨ x = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq106408 (M.op X1 y) x
       have i₂ := eq408844 sF0 X1
       grind)
    | exact superpose eq408844 eq106408
    | exact resolve eq106408 eq408844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106408 eq408844
  have eq427205 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq57172
  have eq427260 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq61 eq427205
    | exact resolve eq427205 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq427205
  have eq427268 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq427260
    | exact resolve eq427260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427260
  have eq1033252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq217728
       have i₂ := eq427268
       grind)
    | exact superpose eq427268 eq217728
    | exact resolve eq217728 eq427268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217728 eq427268
  have eq1033256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1033252
  have eq1033259 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1033256
       have r₂ := eq28
       grind)
    | exact resolve eq1033256 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033256
  have eq1033327 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1033259 eq57
    | exact resolve eq57 eq1033259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1033350 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op x y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1033259 eq100729
    | exact resolve eq100729 eq1033259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034281 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1033327 eq1033259
    | exact resolve eq1033259 eq1033327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033259 eq1033327
  have eq1034425 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1034281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034281
  have eq1035302 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1034425 eq334417
    | exact resolve eq334417 eq1034425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034425
  have eq1035877 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq39 eq1035302
    | exact resolve eq1035302 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035302
  have eq1037027 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) X0) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq211732 X0
       have i₂ := eq1035877 y
       grind)
    | exact superpose eq1035877 eq211732
    | exact resolve eq211732 eq1035877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211732
  have eq1037112 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq414835 x
       have i₂ := eq1035877 y
       grind)
    | exact superpose eq1035877 eq414835
    | exact resolve eq414835 eq1035877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414835 eq1035877
  have eq1037517 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1037112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037112
  have eq1037600 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1037027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037027
  have eq1037776 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1037600 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1037600
    | (have j0 := eq1037600 X0
       grind)
    | exact resolve eq1037600 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037600
  have eq1040637 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq230357 y x
       have i₂ := eq1037517 sF0
       grind)
    | exact superpose eq1037517 eq230357
    | exact resolve eq230357 eq1037517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230357 eq1037517
  have eq1041325 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1040637 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1040637
    | (have j0 := eq1040637 X0
       grind)
    | exact resolve eq1040637 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040637
  have eq1203983 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1033350 eq27
    | (have j1 := eq1033350 (σ y)
       grind)
    | exact resolve eq27 eq1033350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033350
  have eq1204351 : (M.op (σ x) (σ y)) = (M.op y (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1203983 eq77537
    | exact resolve eq77537 eq1203983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77537
  have eq1204352 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op y (σ y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1203983 eq104743
    | exact resolve eq104743 eq1203983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203983
  have eq1204399 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op y (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1204352 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204352
  have eq1204400 : (M.op (σ x) (σ y)) = (M.op y (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1204351
  have eq1205509 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1204400 eq104743
    | exact resolve eq104743 eq1204400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104743 eq1204400
  have eq1205560 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1205509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205509
  have eq1221590 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1041325 eq1204399
    | exact resolve eq1204399 eq1041325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204399
  have eq1222110 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1221590 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221590
  have eq1249181 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1205560 eq1041325
    | exact resolve eq1041325 eq1205560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041325 eq1205560
  have eq1249470 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1249181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249181
  have eq1249757 : (k (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1249470
  have eq1320322 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1249757 eq1037776
    | exact resolve eq1037776 eq1249757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037776 eq1249757
  have eq1320326 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1320322
  have eq1320370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1320326 eq1222110
    | exact resolve eq1222110 eq1320326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222110 eq1320326
  have eq1320374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1320370
  have eq1320397 : x = (M.op x x) := by
    first
    | (have r₁ := eq1320374
       have r₂ := eq28
       grind)
    | exact resolve eq1320374 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320374
  have eq1320527 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ (M.op x x))) = (σ (M.op x (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq121530
       have i₂ := eq1320397
       grind)
    | exact superpose eq1320397 eq121530
    | exact resolve eq121530 eq1320397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121530
  have eq1321785 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ (M.op x x))) = (σ (M.op x (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1320527
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1320527
    | exact resolve eq1320527 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320527
  have eq1321786 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ (M.op x x))) = (σ (M.op x (M.op x x))) := by grind
  clear eq1321785
  have eq1321796 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1321786
       have i₂ := eq1320397
       grind)
    | exact superpose eq1320397 eq1321786
    | exact resolve eq1321786 eq1320397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321786
  have eq1321798 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1321796
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1321796
    | exact resolve eq1321796 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321796
  have eq1321801 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1321798
       have i₂ := eq1320397
       grind)
    | exact superpose eq1320397 eq1321798
    | exact resolve eq1321798 eq1320397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321798
  have eq1321829 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1321801
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1321801
    | exact resolve eq1321801 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1321801
  have eq1321830 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1321829
  have eq1322843 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1321830 eq100729
    | exact resolve eq100729 eq1321830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100729
  have eq1322844 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op x y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1321830 eq100746
    | exact resolve eq100746 eq1321830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323336 : (σ x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq1322844 eq1321830
    | exact resolve eq1321830 eq1322844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321830
  have eq1323400 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq1322843 eq27
    | (have j1 := eq1322843 (σ y)
       grind)
    | exact resolve eq27 eq1322843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1322843
  have eq1323646 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq1323336 eq1322844
    | exact resolve eq1322844 eq1323336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322844 eq1323336
  have eq1323711 : (M.op (σ x) (σ y)) = (σ (k (k y y) y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1323400 eq102406
    | exact resolve eq102406 eq1323400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102406
  have eq1332321 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq1323400 eq334417
    | exact resolve eq334417 eq1323400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334417
  have eq1332322 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1323400 eq335245
    | exact resolve eq335245 eq1323400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1338907 : (M.op (τ (σ x)) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | exact superpose eq1323646 eq335245
    | exact resolve eq335245 eq1323646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335245 eq1323646
  have eq1338933 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq39 eq1338907
    | exact resolve eq1338907 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1338907
  have eq1339387 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1338933
       have i₂ := eq1320397
       grind)
    | exact superpose eq1320397 eq1338933
    | exact resolve eq1338933 eq1320397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320397 eq1338933
  have eq1340828 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1339387 eq107035
    | exact resolve eq107035 eq1339387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107035 eq1339387
  have eq1341240 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | exact superpose eq1340828 eq100746
    | exact resolve eq100746 eq1340828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100746
  have eq1341481 : ∀ X1 X3 : G, (σ (M.op X3 (M.op X1 X1))) = (σ (M.op x X1)) := by
    intro X1 X3
    first
    | exact superpose eq1340828 eq199820
    | exact resolve eq199820 eq1340828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199820
  have eq1343622 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1340828 eq1332322
    | exact resolve eq1332322 eq1340828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332322
  have eq1343700 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1340828 eq1323400
    | exact resolve eq1323400 eq1340828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323400 eq1340828
  have eq1494394 : (M.op (σ x) (σ y)) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq123740 y y y
       have i₂ := eq1323711
       grind)
    | exact superpose eq1323711 eq123740
    | (have j0 := eq123740 y y x
       grind)
    | exact resolve eq123740 eq1323711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123740
  have eq1494612 : (M.op (σ x) (σ y)) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1494394
  have eq1494740 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1494612
  have eq1494771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1494740
       have i₂ := eq1341481 y y
       grind)
    | exact superpose eq1341481 eq1494740
    | exact resolve eq1494740 eq1341481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494740
  have eq1494798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1494771
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1494771
    | exact resolve eq1494771 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494771
  have eq1494820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq1494798
    | exact resolve eq1494798 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494798
  have eq1494827 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1494820
       have r₂ := eq28
       grind)
    | exact resolve eq1494820 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494820
  have eq1494886 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1494827 eq1341240
    | exact resolve eq1341240 eq1494827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1494905 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1343700 eq1494886
    | exact resolve eq1494886 eq1343700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494886
  have eq1495078 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1494905 eq1494827
    | exact resolve eq1494827 eq1494905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494827 eq1494905
  have eq1495149 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1495078
  have eq1495281 : (k y y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq1495330 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1341240 X0 y
       have i₂ := eq1495149
       grind)
    | exact superpose eq1495149 eq1341240
    | exact resolve eq1341240 eq1495149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1495352 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1495330 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1495330
    | (have j0 := eq1495330 X0
       grind)
    | exact resolve eq1495330 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495330
  have eq1495526 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1495149
       have i₂ := eq1495352 y
       grind)
    | exact superpose eq1495352 eq1495149
    | exact resolve eq1495149 eq1495352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495149 eq1495352
  have eq1495531 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1495526
  have eq1495657 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1495531 eq28
    | exact resolve eq28 eq1495531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1495669 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1495531 eq1332321
    | exact resolve eq1332321 eq1495531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332321 eq1495531
  have eq1495694 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40 eq1495669
    | exact resolve eq1495669 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495669
  have eq1497932 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq123618 y
       have i₂ := eq1495694 y
       grind)
    | exact superpose eq1495694 eq123618
    | (have j0 := eq123618 y
       grind)
    | exact resolve eq123618 eq1495694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123618 eq1495694
  have eq1498295 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1497932
  have eq1498479 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1498295
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1498295
    | exact resolve eq1498295 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498295
  have eq1510586 : (M.op (σ x) (σ y)) = (σ (k (M.op y y) y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1323711
       have i₂ := eq1495281
       grind)
    | exact superpose eq1495281 eq1323711
    | exact resolve eq1323711 eq1495281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323711 eq1495281
  have eq1510597 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1510586
  have eq1510602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1510597
       have i₂ := eq1341481 y y
       grind)
    | exact superpose eq1341481 eq1510597
    | exact resolve eq1510597 eq1341481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341481 eq1510597
  have eq1510604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1510602
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1510602
    | exact resolve eq1510602 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510602
  have eq1510605 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1510604
    | exact resolve eq1510604 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510604
  have eq1510606 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1510605
       have r₂ := eq28
       grind)
    | exact resolve eq1510605 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510605
  have eq1510664 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1510606 eq1341240
    | exact resolve eq1341240 eq1510606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341240
  have eq1510689 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1343700 eq1510664
    | exact resolve eq1510664 eq1343700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343700 eq1510664
  have eq1510860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1510689 eq1510606
    | exact resolve eq1510606 eq1510689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510606 eq1510689
  have eq1510862 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1510860
  have eq1510872 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1510862 eq28
    | exact resolve eq28 eq1510862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1510927 : (M.op (τ (σ y)) (τ (σ y))) = (M.op x (τ (σ y))) := by
    first
    | exact superpose eq1510862 eq1343622
    | exact resolve eq1343622 eq1510862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343622 eq1510862
  have eq1512157 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq40 eq1510927
    | exact resolve eq1510927 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1510927
  have eq1516143 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1512157
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1512157
    | exact resolve eq1512157 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1512157
  have eq1520332 : y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1498479
       have i₂ := eq1516143
       grind)
    | exact superpose eq1516143 eq1498479
    | exact resolve eq1498479 eq1516143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498479
  have eq1520375 : y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq1520332
  have eq1522052 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1520375
       have i₂ := eq1516143
       grind)
    | exact superpose eq1516143 eq1520375
    | exact resolve eq1520375 eq1516143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516143 eq1520375
  have eq1522767 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq1522052
    | exact resolve eq1522052 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522052
  have eq1522937 : y = (M.op x y) := by
    first
    | (have r₁ := eq1522767
       have r₂ := eq1495657
       grind)
    | exact resolve eq1522767 eq1495657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495657 eq1522767
  have eq1523012 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1522937 eq21
    | exact resolve eq21 eq1522937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1522937
  have eq1524590 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1523012
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1523012
    | exact resolve eq1523012 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1523012
  have eq1525691 : False := by grind
  exact eq1525691
