import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq39 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq97 X1 X0
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq97 X1 X1
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq97 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq97
  have eq237 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq101 (σ X1) (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq237
    | exact resolve eq237 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq237
  have eq246 : False := by grind
  exact eq246

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq97
    | (have j0 := eq97 (σ X0) (σ X1)
       grind)
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq97 y x
       grind)
    | exact superpose eq97 eq75
    | (have j1 := eq97 y x
       grind)
    | exact resolve eq75 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123 eq97
    | (have j0 := eq97 (σ y) (σ x)
       grind)
    | exact resolve eq97 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq127
       have r₂ := eq27
       grind)
    | exact resolve eq127 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq132 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq132 eq27
    | exact resolve eq27 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq153 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq432 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq132 eq79
    | (have r₁ := eq79
       have r₂ := eq132
       grind)
    | exact resolve eq79 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq132
  have eq433 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq432
  have eq436 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq433 eq123
    | exact resolve eq123 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq440 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq436
  have eq445 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq440
       have r₂ := eq134
       grind)
    | exact resolve eq440 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq440
  have eq451 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq445 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq445
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq445
       grind)
    | exact resolve eq13 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq454 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq451
  have eq458 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq454
    | exact resolve eq454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq458 eq123
    | exact resolve eq123 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq458
  have eq521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq518
  have eq525 : y = (M.op x y) := by
    first
    | (have r₁ := eq521
       have r₂ := eq27
       grind)
    | exact resolve eq521 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq527 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq525 eq20
    | exact resolve eq20 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq525 eq78
    | (have r₁ := eq78
       have r₂ := eq525
       grind)
    | exact resolve eq78 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq538 : x = (M.op y x) ∨ y = (k y x) := by grind
  clear eq533
  have eq545 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq527
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq527
    | exact resolve eq527 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq612 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq545 eq26
    | exact resolve eq26 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq706 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq101
    | (have j0 := eq101 (M.op x y) X0
       grind)
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq101
  have eq718 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq525 eq706
    | (have j0 := eq706 X0
       grind)
    | exact resolve eq706 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq1173 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq718 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq718
    | (have j0 := eq718 x
       grind)
    | exact resolve eq718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq718
  have eq1194 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq612 eq1173
    | exact resolve eq1173 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1208 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1194
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq1194
    | exact resolve eq1194 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1194
  have eq1219 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq545 eq1208
    | exact resolve eq1208 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq612 eq1219
    | exact resolve eq1219 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq1219
  have eq1226 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq1225
       have r₂ := eq27
       grind)
    | exact resolve eq1225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1228 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq1226 eq153
    | exact resolve eq153 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1226
  have eq1230 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq525 eq1228
    | exact resolve eq1228 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1260 : x = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq538
       have i₂ := eq1230
       grind)
    | exact superpose eq1230 eq538
    | exact resolve eq538 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq1264 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1260
       grind)
    | exact superpose eq1260 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1260
       grind)
    | exact resolve eq13 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1276 : (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1264
  have eq1278 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1276
       have i₂ := eq1230
       grind)
    | exact superpose eq1230 eq1276
    | exact resolve eq1276 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230 eq1276
  have eq1281 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1278
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1278
    | exact resolve eq1278 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1278
  have eq1282 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq525 eq1281
    | exact resolve eq1281 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq1281
  have eq1283 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1282
  have eq1292 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1283 eq15
    | exact resolve eq15 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1293 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1292
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1292
    | exact resolve eq1292 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1292
  have eq1294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq545 eq1293
    | exact resolve eq1293 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq1293
  have eq1295 : False := by grind
  exact eq1295

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq411 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq411 (M.op X0 X1)
       grind)
    | exact superpose eq411 eq58
    | exact resolve eq58 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq422 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq411 X0
       grind)
    | exact superpose eq411 eq14
    | exact resolve eq14 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq794 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq70 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq812 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq794 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq815 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq812 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq812 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq812 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq812 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq825 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq815
    | (have j0 := eq815 X0 X1
       grind)
    | exact resolve eq815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq1040 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq422
    | exact resolve eq422 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1042 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq422
    | exact resolve eq422 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq422
  have eq1063 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1040 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq1040
       grind)
    | exact resolve eq13 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : x = (k x (M.op x y)) := by grind
  clear eq1063
  have eq1099 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1042 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq1042
       grind)
    | exact resolve eq13 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1111 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq1099
  have eq1114 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1075 eq45
    | exact resolve eq45 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1075
  have eq1118 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1114
    | exact resolve eq1114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1131 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1118 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1131
  have eq1458 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1132 eq12
    | (have j0 := eq12 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq1132
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq1132
       grind)
    | exact resolve eq12 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1474 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1458
  have eq1475 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1474
  have eq1476 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1118 eq1475
    | exact resolve eq1475 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq1475
  have eq1508 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1476 eq418
    | exact resolve eq418 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq1476
  have eq8963 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1132 eq1508
    | exact resolve eq1508 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq1508
  have eq8990 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq8963
  have eq14204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq14205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14204
    | exact resolve eq14204 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14204
  have eq14216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq14205
       have r₂ := eq27
       grind)
    | exact resolve eq14205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14205
  have eq14219 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14216
    | exact resolve eq14216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14216
  have eq14222 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14219 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14219
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14219
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14219
       grind)
    | exact resolve eq13 eq14219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14219
  have eq14265 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq14222
  have eq14964 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14265 eq99
    | exact resolve eq99 eq14265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq14265
  have eq14989 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq14964
    | exact resolve eq14964 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14964
  have eq14992 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq14989
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq14989
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq14989
       have r₂ := eq13 y x
       grind)
    | exact resolve eq14989 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14989
  have eq15002 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq807 x y
       have i₂ := eq14992
       grind)
    | exact superpose eq14992 eq807
    | (have j0 := eq807 x y
       grind)
    | exact resolve eq807 eq14992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq15004 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq14992
       grind)
    | exact superpose eq14992 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14992
  have eq15005 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15004
  have eq15007 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15002
  have eq15010 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15005
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15005
    | exact resolve eq15005 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15005
  have eq15011 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15010
  have eq15013 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15007
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15007
    | exact resolve eq15007 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15007
  have eq15025 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15013
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15013
    | exact resolve eq15013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15013
  have eq15028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15025
    | exact resolve eq15025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15025
  have eq15029 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq15028
  have eq15032 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15029
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15029
    | exact resolve eq15029 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15029
  have eq15035 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15032
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15032
    | exact resolve eq15032 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15032
  have eq15036 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15011
       grind)
    | exact superpose eq15011 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15011
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15011
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15011
       grind)
    | exact resolve eq12 eq15011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15011
  have eq15081 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15036
  have eq15082 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15081
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15081
    | exact resolve eq15081 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15081
  have eq15083 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15082
  have eq15084 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15083
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15083
    | exact resolve eq15083 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15083
  have eq15138 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15035 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15035
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15035
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15035
       grind)
    | exact resolve eq12 eq15035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15035
  have eq15183 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15138
  have eq15184 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15183
    | exact resolve eq15183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15183
  have eq15185 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15184
  have eq15186 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15185
    | exact resolve eq15185 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15185
  have eq15205 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15084
       grind)
    | exact superpose eq15084 eq44
    | exact resolve eq44 eq15084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq15084
  have eq15225 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15205
    | exact resolve eq15205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15205
  have eq15290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15225 eq15186
    | exact resolve eq15186 eq15225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15186 eq15225
  have eq15295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15290
  have eq15297 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15295
       have r₂ := eq27
       grind)
    | exact resolve eq15295 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15295
  have eq15375 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15297 eq1111
    | exact resolve eq1111 eq15297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq15297
  have eq15403 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15375 eq55
    | exact resolve eq55 eq15375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq15375
  have eq15432 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq15403
    | exact resolve eq15403 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15403
  have eq15437 : x = (k x y) := by
    first
    | (have r₁ := eq15432
       have r₂ := eq50
       grind)
    | exact resolve eq15432 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq15432
  have eq15448 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq825 x y
       have i₂ := eq15437
       grind)
    | exact superpose eq15437 eq825
    | (have j0 := eq825 x y
       grind)
    | exact resolve eq825 eq15437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq15451 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15437
       grind)
    | exact superpose eq15437 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15452 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq15451
  have eq15455 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15448
  have eq15457 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15452
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15452
    | exact resolve eq15452 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15452
  have eq15460 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15455
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15455
    | exact resolve eq15455 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15455
  have eq15471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15460
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15460
    | exact resolve eq15460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15460
  have eq15475 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15471
    | exact resolve eq15471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15471
  have eq15478 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15475
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15475
    | exact resolve eq15475 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15475
  have eq15481 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15478
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15478
    | exact resolve eq15478 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15478
  have eq15482 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15481
    | exact resolve eq15481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15481
  have eq15517 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15482 eq27
    | exact resolve eq27 eq15482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15482
  have eq15581 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15457
       grind)
    | exact superpose eq15457 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15457
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15457
       grind)
    | exact resolve eq12 eq15457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15457
  have eq15626 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq15581
  have eq15627 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15626
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15626
    | exact resolve eq15626 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15626
  have eq15628 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq15627
  have eq15629 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15628
       have i₂ := eq15437
       grind)
    | exact superpose eq15437 eq15628
    | exact resolve eq15628 eq15437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15437 eq15628
  have eq15630 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15629
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15629
    | exact resolve eq15629 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15629
  have eq15631 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15630 eq20
    | exact resolve eq20 eq15630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15630
  have eq15768 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15631
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15631
    | exact resolve eq15631 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15631
  have eq15775 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15768 eq26
    | exact resolve eq26 eq15768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15768
  have eq15920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8990 eq15775
    | exact resolve eq15775 eq8990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8990 eq15775
  have eq15930 : x = (M.op x y) := by
    first
    | (have r₁ := eq15920
       have r₂ := eq27
       grind)
    | exact resolve eq15920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15920
  have eq16819 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15930 eq20
    | exact resolve eq20 eq15930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16900 : x = (M.op x x) := by
    first
    | exact superpose eq15930 eq1040
    | exact resolve eq1040 eq15930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq16968 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16819
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16819
    | exact resolve eq16819 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16819
  have eq17152 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq16900
       grind)
    | exact superpose eq16900 eq56
    | exact resolve eq56 eq16900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq17263 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq15930 eq17152
    | exact resolve eq17152 eq15930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17152
  have eq17284 : y = (M.op x y) := by
    first
    | (have i₁ := eq17263
       have i₂ := eq16900
       grind)
    | exact superpose eq16900 eq17263
    | exact resolve eq17263 eq16900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16900 eq17263
  have eq17290 : y = (M.op x y) := by
    first
    | (have i₁ := eq17284
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17284
    | exact resolve eq17284 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17284
  have eq17292 : x = y := by
    first
    | exact superpose eq15930 eq17290
    | exact resolve eq17290 eq15930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15930 eq17290
  have eq19027 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17292
       grind)
    | exact superpose eq17292 eq24
    | exact resolve eq24 eq17292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17292
  have eq19179 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19027
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19027
    | exact resolve eq19027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19027
  have eq19244 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16968 eq19179
    | exact resolve eq19179 eq16968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19179
  have eq19375 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19244 eq15517
    | (have r₁ := eq15517
       have r₂ := eq19244
       grind)
    | exact resolve eq15517 eq19244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15517 eq19244
  have eq19377 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19375
  have eq19380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16968 eq19377
    | exact resolve eq19377 eq16968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968 eq19377
  have eq19451 : False := by grind
  exact eq19451

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq97 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq132 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq13 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq143 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq136 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq147 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq380 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq132
    | (have j1 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq132 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq132
  have eq383 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq380
  have eq385 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq383
       grind)
    | exact superpose eq383 eq9
    | exact resolve eq9 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq929 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq97 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq953 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq929 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq929
    | exact resolve eq929 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq2200 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq385 x
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq385
    | exact resolve eq385 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2330 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq2200
       grind)
    | exact superpose eq2200 eq9
    | exact resolve eq9 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2375 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq147 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq147
    | (have j0 := eq147 (τ X0) (τ X1)
       grind)
    | exact resolve eq147 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2393 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2375 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2375
    | (have j0 := eq2375 X0 X1
       grind)
    | exact resolve eq2375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2399 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2393 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2393
    | (have j0 := eq2393 X0 X1
       grind)
    | exact resolve eq2393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq2405 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2399 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2399
    | (have j0 := eq2399 X0 X1
       grind)
    | exact resolve eq2399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2410 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2405 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2405
    | (have j0 := eq2405 X0 X1
       grind)
    | exact resolve eq2405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2415 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2410 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2410
    | (have j0 := eq2410 X0 X1
       grind)
    | exact resolve eq2410 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq2420 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2415 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2415
    | (have j0 := eq2415 X0 X1
       grind)
    | exact resolve eq2415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq3411 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq103 x X0 x
       have i₂ := eq2330 X0
       grind)
    | exact superpose eq2330 eq103
    | exact resolve eq103 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq2330
  have eq5214 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq953 (σ x) (σ y)
       have i₂ := eq3411 X0
       grind)
    | exact superpose eq3411 eq953
    | (have j1 := eq3411 X0
       grind)
    | exact resolve eq953 eq3411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3411
  have eq5890 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq5214 X0
       grind)
    | exact superpose eq5214 eq12
    | (have j1 := eq5214 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq5214 X0
       grind)
    | (have r₁ := eq12 (M.op x X0) x
       have r₂ := eq5214 X0
       grind)
    | exact resolve eq12 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq5952 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq5890 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890
  have eq5981 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq5952 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq5952
    | (have j0 := eq5952 X0
       grind)
    | exact resolve eq5952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5952
  have eq6004 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq5981 X0
       grind)
    | exact superpose eq5981 eq10
    | (have j1 := eq5981 X0
       grind)
    | exact resolve eq10 eq5981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981
  have eq6060 : ∀ X0 : G, x = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6004 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6004
    | (have j0 := eq6004 X0
       grind)
    | exact resolve eq6004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6004
  have eq6080 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2420 x x
       have i₂ := eq6060 X0
       grind)
    | exact superpose eq6060 eq2420
    | (have j0 := eq2420 x x
       have j1 := eq6060 X0
       grind)
    | (have r₁ := eq2420 x x
       have r₂ := eq6060 X0
       grind)
    | exact resolve eq2420 eq6060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060
  have eq6081 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6080 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6080
  have eq6082 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6081
  have eq6297 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq6082 X1
       grind)
    | exact superpose eq6082 eq9
    | (have j1 := eq6082 (M.op x X0)
       grind)
    | exact resolve eq9 eq6082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6082
  have eq6389 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq6297 X0 X1
       have i₂ := eq953 x X0
       grind)
    | (have i₁ := eq6297 X0 X1
       have i₂ := eq953 x (M.op x X0)
       grind)
    | exact superpose eq953 eq6297
    | (have j0 := eq6297 X0 X0
       grind)
    | exact resolve eq6297 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6297
  have eq6678 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6389 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389
  have eq6679 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6678 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6678
  have eq6893 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq6679 X0
       grind)
    | exact superpose eq6679 eq385
    | exact resolve eq385 eq6679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq6911 : ∀ X0 : G, x ≠ x ∨ (M.op x (M.op x X0)) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op x X0) x
       have i₂ := eq6679 X0
       grind)
    | exact superpose eq6679 eq12
    | (have j0 := eq12 (M.op x X0) x
       grind)
    | (have r₁ := eq12 (M.op x X0) x
       have r₂ := eq6679 X0
       grind)
    | exact resolve eq12 eq6679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6974 : ∀ X0 : G, (M.op x (M.op x X0)) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6911 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6911
  have eq6983 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6974 X0
       have i₂ := eq953 x X0
       grind)
    | (have i₁ := eq6974 X0
       have i₂ := eq953 x (M.op x X0)
       grind)
    | exact superpose eq953 eq6974
    | exact resolve eq6974 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6974
  have eq7518 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq953 (σ x) (σ y)
       have i₂ := eq6893 X0
       grind)
    | exact superpose eq6893 eq953
    | (have j1 := eq6893 X0
       grind)
    | exact resolve eq953 eq6893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq6893
  have eq7700 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq7518 X0
       grind)
    | exact superpose eq7518 eq12
    | (have j1 := eq7518 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq7518 X0
       grind)
    | (have r₁ := eq12 x X0
       have r₂ := eq7518 X0
       grind)
    | exact resolve eq12 eq7518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7518
  have eq7762 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7700
  have eq7791 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7762 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq7762
    | (have j0 := eq7762 X0
       grind)
    | exact resolve eq7762 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7762
  have eq7940 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq7791 X0
       grind)
    | exact superpose eq7791 eq10
    | (have j1 := eq7791 X0
       grind)
    | exact resolve eq10 eq7791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7791
  have eq7998 : ∀ X0 : G, x = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7940 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7940
    | (have j0 := eq7940 X0
       grind)
    | exact resolve eq7940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7940
  have eq8207 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2420 x x
       have i₂ := eq7998 X0
       grind)
    | exact superpose eq7998 eq2420
    | (have j0 := eq2420 x x
       have j1 := eq7998 x
       grind)
    | (have r₁ := eq2420 x x
       have r₂ := eq7998 X0
       grind)
    | exact resolve eq2420 eq7998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420 eq7998
  have eq8208 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8207 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207
  have eq8209 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8208 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8208
  have eq8297 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq8209 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8209
  have eq8298 : x = (M.op x x) := by grind
  clear eq8297
  have eq8513 : x = (k x x) := by
    first
    | (have i₁ := eq6983 x
       have i₂ := eq8298
       grind)
    | exact superpose eq8298 eq6983
    | exact resolve eq6983 eq8298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6983
  have eq8516 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq8298
       grind)
    | exact superpose eq8298 eq9
    | exact resolve eq9 eq8298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8298
  have eq8626 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8516 X0
       have i₂ := eq6679 X0
       grind)
    | exact superpose eq6679 eq8516
    | exact resolve eq8516 eq6679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6679 eq8516
  have eq8798 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq147 x x
       have i₂ := eq8513
       grind)
    | exact superpose eq8513 eq147
    | (have j0 := eq147 x x
       grind)
    | exact resolve eq147 eq8513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq8513
  have eq8815 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8798
  have eq8816 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8815
  have eq9155 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq8626 X0
       grind)
    | exact superpose eq8626 eq9
    | exact resolve eq9 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9326 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9155 X0 X1
       have i₂ := eq8626 X1
       grind)
    | exact superpose eq8626 eq9155
    | exact resolve eq9155 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9155
  have eq14768 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq8816
       grind)
    | exact superpose eq8816 eq9
    | exact resolve eq9 eq8816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8816
  have eq14882 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14768 X0
       have i₂ := eq9326 X0 (σ x)
       grind)
    | exact superpose eq9326 eq14768
    | exact resolve eq14768 eq9326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9326 eq14768
  have eq14946 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14882 (σ y)
       grind)
    | exact superpose eq14882 eq16
    | exact resolve eq16 eq14882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14882
  have eq15143 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq14946
       have i₂ := eq8626 y
       grind)
    | exact superpose eq8626 eq14946
    | exact resolve eq14946 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8626 eq14946
  have eq15144 : False := by grind
  exact eq15144

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq97 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq132 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq144 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq135
    | (have j0 := eq135 X0 X1
       grind)
    | exact resolve eq135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq380 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq132
    | (have j1 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq132 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq132
  have eq383 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq380
  have eq385 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq383
       grind)
    | exact superpose eq383 eq9
    | exact resolve eq9 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq929 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq97 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq953 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq929 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq929
    | exact resolve eq929 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq2263 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq385 x
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq385
    | exact resolve eq385 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2321 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq144 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq144
    | (have j0 := eq144 (τ X0) (τ X1)
       grind)
    | exact resolve eq144 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2343 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2321 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2321
    | (have j0 := eq2321 X0 X1
       grind)
    | exact resolve eq2321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2355 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2343 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2343
    | (have j0 := eq2343 X0 X1
       grind)
    | exact resolve eq2343 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq2366 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2355 X0 X1
       have i₂ := eq17 X1 (τ X0)
       grind)
    | exact superpose eq17 eq2355
    | (have j0 := eq2355 X0 X1
       grind)
    | exact resolve eq2355 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2355
  have eq2372 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2366 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2366
    | (have j0 := eq2366 X0 X1
       grind)
    | exact resolve eq2366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2377 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2372 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2372
    | (have j0 := eq2372 X0 X1
       grind)
    | exact resolve eq2372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372
  have eq2382 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2377 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2377
    | (have j0 := eq2377 X0 X1
       grind)
    | exact resolve eq2377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2387 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2382 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2382
    | (have j0 := eq2382 X0 X1
       grind)
    | exact resolve eq2382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq2393 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq2263
       grind)
    | exact superpose eq2263 eq9
    | exact resolve eq9 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq3311 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq103 x X0 x
       have i₂ := eq2393 X0
       grind)
    | exact superpose eq2393 eq103
    | exact resolve eq103 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq2393
  have eq5403 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq953 (σ x) (σ y)
       have i₂ := eq3311 X0
       grind)
    | exact superpose eq3311 eq953
    | (have j1 := eq3311 X0
       grind)
    | exact resolve eq953 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq5930 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq5403 X0
       grind)
    | exact superpose eq5403 eq12
    | (have j1 := eq5403 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq5403 X0
       grind)
    | (have r₁ := eq12 (M.op x X0) x
       have r₂ := eq5403 X0
       grind)
    | exact resolve eq12 eq5403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq5992 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq5930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930
  have eq6021 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq5992 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq5992
    | (have j0 := eq5992 X0
       grind)
    | exact resolve eq5992 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992
  have eq6043 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq6021 X0
       grind)
    | exact superpose eq6021 eq10
    | (have j1 := eq6021 X0
       grind)
    | exact resolve eq10 eq6021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6021
  have eq6097 : ∀ X0 : G, x = (k x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6043 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6043
    | (have j0 := eq6043 X0
       grind)
    | exact resolve eq6043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043
  have eq6115 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2387 x x
       have i₂ := eq6097 X0
       grind)
    | exact superpose eq6097 eq2387
    | (have j0 := eq2387 x x
       have j1 := eq6097 X0
       grind)
    | (have r₁ := eq2387 x x
       have r₂ := eq6097 X0
       grind)
    | exact resolve eq2387 eq6097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6097
  have eq6116 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6115
  have eq6117 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6116
  have eq6133 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq6117 X1
       grind)
    | exact superpose eq6117 eq9
    | (have j1 := eq6117 (M.op x X0)
       grind)
    | exact resolve eq9 eq6117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117
  have eq6225 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op (M.op x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq6133 X0 X1
       have i₂ := eq953 x X0
       grind)
    | (have i₁ := eq6133 X0 X1
       have i₂ := eq953 x (M.op x X0)
       grind)
    | exact superpose eq953 eq6133
    | (have j0 := eq6133 X0 X0
       grind)
    | exact resolve eq6133 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6133
  have eq6323 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6225 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6225
  have eq6324 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6323
  have eq6539 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq6324 X0
       grind)
    | exact superpose eq6324 eq385
    | exact resolve eq385 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq6557 : ∀ X0 : G, x ≠ x ∨ (M.op x (M.op x X0)) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op x X0) x
       have i₂ := eq6324 X0
       grind)
    | exact superpose eq6324 eq12
    | (have j0 := eq12 (M.op x X0) x
       grind)
    | (have r₁ := eq12 (M.op x X0) x
       have r₂ := eq6324 X0
       grind)
    | exact resolve eq12 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6620 : ∀ X0 : G, (M.op x (M.op x X0)) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq6557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq6629 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq6620 X0
       have i₂ := eq953 x X0
       grind)
    | (have i₁ := eq6620 X0
       have i₂ := eq953 x (M.op x X0)
       grind)
    | exact superpose eq953 eq6620
    | exact resolve eq6620 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6620
  have eq7357 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq953 (σ x) (σ y)
       have i₂ := eq6539 X0
       grind)
    | exact superpose eq6539 eq953
    | (have j1 := eq6539 X0
       grind)
    | exact resolve eq953 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq6539
  have eq7605 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq7357 X0
       grind)
    | exact superpose eq7357 eq12
    | (have j1 := eq7357 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq7357 X0
       grind)
    | (have r₁ := eq12 x X0
       have r₂ := eq7357 X0
       grind)
    | exact resolve eq12 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7357
  have eq7667 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7605
  have eq7696 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7667 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq7667
    | (have j0 := eq7667 X0
       grind)
    | exact resolve eq7667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7667
  have eq7719 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq7696 X0
       grind)
    | exact superpose eq7696 eq10
    | (have j1 := eq7696 X0
       grind)
    | exact resolve eq10 eq7696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696
  have eq7773 : ∀ X0 : G, x = (k x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7719 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7719
    | (have j0 := eq7719 X0
       grind)
    | exact resolve eq7719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7719
  have eq7792 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2387 x x
       have i₂ := eq7773 X0
       grind)
    | exact superpose eq7773 eq2387
    | (have j0 := eq2387 x x
       have j1 := eq7773 x
       grind)
    | (have r₁ := eq2387 x x
       have r₂ := eq7773 X0
       grind)
    | exact resolve eq2387 eq7773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387 eq7773
  have eq7793 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7792 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7792
  have eq7794 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7793 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7793
  have eq7879 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq7794 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7794
  have eq7880 : x = (M.op x x) := by grind
  clear eq7879
  have eq7956 : x = (k x x) := by
    first
    | (have i₁ := eq6629 x
       have i₂ := eq7880
       grind)
    | exact superpose eq7880 eq6629
    | exact resolve eq6629 eq7880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6629
  have eq7960 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq7880
       grind)
    | exact superpose eq7880 eq9
    | exact resolve eq9 eq7880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq8069 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7960 X0
       have i₂ := eq6324 X0
       grind)
    | exact superpose eq6324 eq7960
    | exact resolve eq7960 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324 eq7960
  have eq8098 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq144 x x
       have i₂ := eq7956
       grind)
    | exact superpose eq7956 eq144
    | (have j0 := eq144 x x
       grind)
    | exact resolve eq144 eq7956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq7956
  have eq8112 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8098
  have eq8113 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8112
  have eq8269 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq8069 X0
       grind)
    | exact superpose eq8069 eq9
    | exact resolve eq9 eq8069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8429 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8269 X0 X1
       have i₂ := eq8069 X1
       grind)
    | exact superpose eq8069 eq8269
    | exact resolve eq8269 eq8069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8269
  have eq14363 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq8113
       grind)
    | exact superpose eq8113 eq9
    | exact resolve eq9 eq8113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8113
  have eq14477 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14363 X0
       have i₂ := eq8429 X0 (σ x)
       grind)
    | exact superpose eq8429 eq14363
    | exact resolve eq14363 eq8429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8429 eq14363
  have eq14534 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14477 (σ y)
       grind)
    | exact superpose eq14477 eq16
    | exact resolve eq16 eq14477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14477
  have eq14728 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq14534
       have i₂ := eq8069 y
       grind)
    | exact superpose eq8069 eq14534
    | exact resolve eq14534 eq8069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8069 eq14534
  have eq14729 : False := by grind
  exact eq14729

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq78 y x
       grind)
    | exact superpose eq78 eq75
    | (have j1 := eq78 x x
       grind)
    | exact resolve eq75 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq110 eq78
    | (have j0 := eq78 x (σ x)
       grind)
    | exact resolve eq78 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq727
    | exact resolve eq727 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq731 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq728
       have r₂ := eq27
       grind)
    | exact resolve eq728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq735 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq731 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq731
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq731
       grind)
    | exact resolve eq13 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq746 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq735
  have eq748 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq746 eq49
    | exact resolve eq49 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq746
  have eq752 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq748
    | exact resolve eq748 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq748
  have eq755 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq78 x x
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq78
    | (have j0 := eq78 x x
       grind)
    | exact resolve eq78 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq756 : x = (M.op x x) := by grind
  clear eq755
  have eq795 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq53
    | exact resolve eq53 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq796 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq50
    | exact resolve eq50 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq797 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq756
       grind)
    | exact resolve eq13 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq14
    | exact resolve eq14 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq14
    | exact resolve eq14 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq810 : x = (k x x) := by grind
  clear eq797
  have eq812 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq810
       grind)
    | exact superpose eq810 eq43
    | exact resolve eq43 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq810
  have eq816 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq812
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq812
    | exact resolve eq812 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq812
  have eq834 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq816 eq78
    | (have j0 := eq78 x (σ x)
       grind)
    | exact resolve eq78 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq816
  have eq835 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq834
  have eq839 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq835 eq51
    | exact resolve eq51 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq835
  have eq945 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq799 (M.op x X0)
       have i₂ := eq798 X0
       grind)
    | exact superpose eq798 eq799
    | exact resolve eq799 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq795 eq799
    | exact resolve eq799 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq948 eq795
    | exact resolve eq795 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq948
  have eq994 : y = (M.op x y) := by
    first
    | exact superpose eq976 eq796
    | exact resolve eq796 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq976
  have eq1007 : y = (M.op x y) := by
    first
    | (have i₁ := eq994
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq994
    | exact resolve eq994 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq994
  have eq1008 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1007 eq20
    | exact resolve eq20 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1007
  have eq1039 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1008
    | exact resolve eq1008 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1008
  have eq1041 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1039 eq26
    | exact resolve eq26 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1039 eq839
    | exact resolve eq839 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq1039
  have eq1288 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq798 X0
       have i₂ := eq945 X0
       grind)
    | exact superpose eq945 eq798
    | exact resolve eq798 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq945
  have eq1314 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq1288 X0
       grind)
    | exact superpose eq1288 eq799
    | exact resolve eq799 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq1288
  have eq1345 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1314 X0
       grind)
    | exact superpose eq1314 eq14
    | exact resolve eq14 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1368 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1345 X0 X1
       have i₂ := eq1314 X1
       grind)
    | exact superpose eq1314 eq1345
    | exact resolve eq1345 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314 eq1345
  have eq1626 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq1368
    | (have j0 := eq1368 (σ y) (σ x)
       grind)
    | exact resolve eq1368 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1368
  have eq1670 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1626 eq1056
    | exact resolve eq1056 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056 eq1626
  have eq1687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1041 eq1670
    | exact resolve eq1670 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq1670
  have eq1689 : False := by grind
  exact eq1689

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  clear eq39
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
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq741 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq741 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq741 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq747 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq16
    | exact resolve eq16 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq16
    | exact resolve eq16 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq743 (M.op X0 X1)
       grind)
    | exact superpose eq743 eq16
    | exact resolve eq16 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : x = (M.op (M.op (k x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq743 x
       grind)
    | exact superpose eq743 eq177
    | exact resolve eq177 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq747 X0 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq747
    | exact resolve eq747 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq870 X0
       have i₂ := eq743 (k X0 X0)
       grind)
    | exact superpose eq743 eq870
    | exact resolve eq870 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1024 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq749 (k (M.op X0 x) (M.op X0 x)) x
       have i₂ := eq749 X0 x
       grind)
    | exact superpose eq749 eq749
    | exact resolve eq749 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1024 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1024
    | exact resolve eq1024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (k X0 X0) X0
       have i₂ := eq1024 X0
       grind)
    | exact superpose eq1024 eq16
    | exact resolve eq16 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1051 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (k (k X0 X0) (k X0 X0)) X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq748 (k X0 X0) X0
       have i₂ := eq1024 X0
       grind)
    | exact superpose eq1024 eq748
    | exact resolve eq748 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1054 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1051 X0
       have i₂ := eq923 X0
       grind)
    | exact superpose eq923 eq1051
    | exact resolve eq1051 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq1051
  have eq1072 : (k x x) = (M.op (M.op (k x x) (M.op x y)) (k x x)) := by
    first
    | (have i₁ := eq177 (k x x)
       have i₂ := eq1054 x
       grind)
    | exact superpose eq1054 eq177
    | exact resolve eq177 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1054
  have eq1092 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1041 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1041
    | exact resolve eq1041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1454 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1049 (M.op X1 X0) X0
       have i₂ := eq749 X1 X0
       grind)
    | exact superpose eq749 eq1049
    | exact resolve eq1049 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1049 X0 (M.op X0 X1)
       have i₂ := eq748 X0 X1
       grind)
    | exact superpose eq748 eq1049
    | exact resolve eq1049 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq756 eq1049
    | exact resolve eq1049 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq2568 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq608
       grind)
    | exact superpose eq608 eq40
    | exact resolve eq40 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq2569 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2568
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2568
    | exact resolve eq2568 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2571 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2569
    | exact resolve eq2569 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569
  have eq25438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2571 eq610
    | exact resolve eq610 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25451 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25438
       have r₂ := eq27
       grind)
    | exact resolve eq25438 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25438
  have eq25460 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25451 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq25451
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq25451
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq25451
       grind)
    | exact resolve eq12 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25489 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq25451
  have eq25497 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25460
       have r₂ := eq25489
       grind)
    | exact resolve eq25460 eq25489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25460 eq25489
  have eq25501 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25497
       have r₂ := eq26
       grind)
    | exact resolve eq25497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25497
  have eq25505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2571 eq25501
    | exact resolve eq25501 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25501
  have eq25507 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25505
       have r₂ := eq27
       grind)
    | exact resolve eq25505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25505
  have eq25512 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25507 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25507
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25507
       grind)
    | exact resolve eq13 eq25507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25513 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq25507 eq16
    | exact resolve eq16 eq25507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25531 : (σ x) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25507 eq749
    | exact resolve eq749 eq25507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25534 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25507 eq1462
    | exact resolve eq1462 eq25507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25537 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq25512
  have eq25541 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq25534
       have i₂ := eq743 sF3
       grind)
    | exact superpose eq743 eq25534
    | exact resolve eq25534 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25534
  have eq25556 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq25513 x
       have i₂ := eq1462 sF3 x
       grind)
    | exact superpose eq1462 eq25513
    | exact resolve eq25513 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25513
  have eq25557 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq25537
       have i₂ := eq743 sF3
       grind)
    | exact superpose eq743 eq25537
    | exact resolve eq25537 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25537
  have eq25568 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2571 eq25557
    | exact resolve eq25557 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571 eq25557
  have eq25574 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25541 eq25568
    | exact resolve eq25568 eq25541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25568
  have eq25580 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq25574
       grind)
    | exact superpose eq25574 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq25574
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq25574
       grind)
    | exact resolve eq12 eq25574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25609 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq25574
  have eq25617 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25580
       have r₂ := eq25609
       grind)
    | exact resolve eq25580 eq25609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25580 eq25609
  have eq25621 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25617
       have r₂ := eq18
       grind)
    | exact resolve eq25617 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25617
  have eq26159 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq25621
       grind)
    | exact superpose eq25621 eq40
    | exact resolve eq40 eq25621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq25621
  have eq26166 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq26159
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26159
    | exact resolve eq26159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26159
  have eq26170 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq26166
    | exact resolve eq26166 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26166
  have eq26276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26170 eq610
    | exact resolve eq610 eq26170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq26289 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq26276
       have r₂ := eq27
       grind)
    | exact resolve eq26276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26276
  have eq28198 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq25541 eq25531
    | exact resolve eq25531 eq25541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28209 : ∀ X0 : G, (M.op (M.op (M.op (k (σ y) (σ y)) X0) (σ x)) X0) = X0 ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq25531 eq16
    | exact resolve eq16 eq25531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25531
  have eq28235 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq28198
  have eq28260 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq25541 eq28209
    | exact resolve eq28209 eq25541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25541 eq28209
  have eq28284 : ∀ X0 : G, (M.op x y) = (M.op y x) ∨ (M.op (σ x) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq25556 eq28260
    | exact resolve eq28260 eq25556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28260
  have eq29244 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28235 eq25507
    | exact resolve eq25507 eq28235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25507 eq28235
  have eq29278 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq29244
  have eq29366 : y ≠ (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  have eq34096 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (k (M.op (σ y) X0) (M.op (σ y) X0))) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq25556 eq747
    | exact resolve eq747 eq25556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq25556
  have eq34114 : ∀ X0 : G, (σ x) = (M.op (k (M.op (σ y) X0) (M.op (σ y) X0)) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28284 eq34096
    | exact resolve eq34096 eq28284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34096
  have eq34139 : ∀ X0 : G, (σ x) = (M.op (k (M.op (σ x) X0) (M.op (σ x) X0)) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29278 eq34114
    | exact resolve eq34114 eq29278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29278 eq34114
  have eq34154 : ∀ X0 : G, (σ x) = (M.op (k X0 X0) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28284 eq34139
    | exact resolve eq34139 eq28284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34139
  have eq34566 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq34154 eq1049
    | exact resolve eq1049 eq34154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049 eq34154
  have eq34617 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28284 eq34566
    | exact resolve eq34566 eq28284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28284 eq34566
  have eq34630 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq34617 eq743
    | exact resolve eq743 eq34617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34617
  have eq34919 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq34630 eq141
    | exact resolve eq141 eq34630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq34630
  have eq34953 : (M.op x y) = (M.op y x) ∨ x = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq34919
    | exact resolve eq34919 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34919
  have eq35012 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1454 x y
       have i₂ := eq34953
       grind)
    | exact superpose eq34953 eq1454
    | exact resolve eq1454 eq34953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34953
  have eq35020 : y = (M.op y x) ∨ x = (k x x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1463 eq35012
    | exact resolve eq35012 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35012
  have eq35137 : x = (M.op (M.op x y) x) ∨ x = (k x x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1454 x y
       have i₂ := eq35020
       grind)
    | exact superpose eq35020 eq1454
    | exact resolve eq1454 eq35020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq35020
  have eq35147 : x = (M.op (M.op x y) x) ∨ x = (k x x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq35137
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35137
    | exact resolve eq35137 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35137
  have eq35148 : x = (k x x) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq35147
  have eq35179 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq35148
       grind)
    | exact superpose eq35148 eq1072
    | exact resolve eq1072 eq35148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq35148
  have eq35226 : x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1463 eq35179
    | exact resolve eq35179 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq35179
  have eq35227 : x = (M.op (M.op x y) x) := by grind
  clear eq35226
  have eq53128 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26289 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26289
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26289
       grind)
    | exact resolve eq12 eq26289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53165 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq26289
  have eq53183 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq53128
       have r₂ := eq53165
       grind)
    | exact resolve eq53128 eq53165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53128 eq53165
  have eq53187 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq53183
       have r₂ := eq26
       grind)
    | exact resolve eq53183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53183
  have eq53191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26170 eq53187
    | exact resolve eq53187 eq26170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53187
  have eq53193 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq53191
       have r₂ := eq27
       grind)
    | exact resolve eq53191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53191
  have eq53208 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq53193 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq53193
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq53193
       grind)
    | exact resolve eq13 eq53193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53230 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq53193 eq1462
    | exact resolve eq1462 eq53193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53193
  have eq53241 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq53208
  have eq53259 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq53230
       have i₂ := eq743 sF3
       grind)
    | exact superpose eq743 eq53230
    | exact resolve eq53230 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53230
  have eq53275 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq53241
       have i₂ := eq743 sF3
       grind)
    | exact superpose eq743 eq53241
    | exact resolve eq53241 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53241
  have eq53286 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26170 eq53275
    | exact resolve eq53275 eq26170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26170 eq53275
  have eq53292 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq53259 eq53286
    | exact resolve eq53286 eq53259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53259 eq53286
  have eq53293 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq53292
  have eq53337 : x = (M.op (k y y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq749 y x
       have i₂ := eq53293
       grind)
    | exact superpose eq53293 eq749
    | exact resolve eq749 eq53293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq53340 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1462 y x
       have i₂ := eq53293
       grind)
    | exact superpose eq53293 eq1462
    | exact resolve eq1462 eq53293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462 eq53293
  have eq53363 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq53340
       have i₂ := eq743 y
       grind)
    | exact superpose eq743 eq53340
    | exact resolve eq53340 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53340
  have eq53862 : (k y y) = (M.op (M.op (k (k y y) (k y y)) x) (k y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq748 (k y y) x
       have i₂ := eq53337
       grind)
    | exact superpose eq53337 eq748
    | exact resolve eq748 eq53337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq53894 : y = (M.op (M.op (k y y) x) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53363 eq53862
    | exact resolve eq53862 eq53363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53363 eq53862
  have eq53925 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53337 eq53894
    | exact resolve eq53894 eq53337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53337 eq53894
  have eq53945 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53925
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53925
    | exact resolve eq53925 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq53925
  have eq53985 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53945 eq28
    | exact resolve eq28 eq53945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq53945
  have eq54110 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq53985
    | exact resolve eq53985 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq53985
  have eq54111 : y = (M.op x y) := by grind
  clear eq54110
  have eq54133 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq54111
       grind)
    | exact superpose eq54111 eq24
    | exact resolve eq24 eq54111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq54290 : (M.op x y) ≠ (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq29366
       have i₂ := eq54111
       grind)
    | exact superpose eq54111 eq29366
    | (have r₁ := eq29366
       have r₂ := eq54111
       grind)
    | exact resolve eq29366 eq54111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29366 eq54111
  have eq54373 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq54290
  have eq54438 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35227 eq54373
    | exact resolve eq54373 eq35227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54373
  have eq54625 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq54133 eq20
    | exact resolve eq20 eq54133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54628 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq54133 eq15
    | exact resolve eq15 eq54133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55406 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54438 eq54628
    | exact resolve eq54628 eq54438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54438 eq54628
  have eq55413 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq55406
    | exact resolve eq55406 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq55406
  have eq55414 : x = (M.op x y) := by grind
  clear eq55413
  have eq55514 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq55414
       grind)
    | exact superpose eq55414 eq22
    | exact resolve eq22 eq55414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq55690 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq35227
       have i₂ := eq55414
       grind)
    | exact superpose eq55414 eq35227
    | exact resolve eq35227 eq55414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35227 eq55414
  have eq55797 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq55690
       have i₂ := eq743 sF0
       grind)
    | exact superpose eq743 eq55690
    | exact resolve eq55690 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55690
  have eq55952 : (σ x) = (σ y) := by
    first
    | exact superpose eq55514 eq54133
    | exact resolve eq54133 eq55514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54133
  have eq55953 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq55514 eq20
    | exact resolve eq20 eq55514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55514
  have eq56385 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq55952 eq26
    | exact resolve eq26 eq55952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq56609 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq56385
       have i₂ := eq743 sF2
       grind)
    | exact superpose eq743 eq56385
    | exact resolve eq56385 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56385
  have eq57230 : (σ (σ (M.op x y))) = (M.op (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq55797 eq1092
    | exact resolve eq1092 eq55797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq55797
  have eq57242 : (σ (σ (M.op x y))) = (k (σ (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq57230
       have i₂ := eq743 (σ (σ sF0))
       grind)
    | exact superpose eq743 eq57230
    | exact resolve eq57230 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq57230
  have eq57276 : (σ (σ (M.op x y))) = (σ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq57242
       have i₂ := eq10 (σ sF0) (σ sF0)
       grind)
    | exact superpose eq10 eq57242
    | exact resolve eq57242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57242
  have eq57292 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ (M.op x y))) := by
    first
    | (have i₁ := eq57276
       have i₂ := eq10 sF0 sF0
       grind)
    | exact superpose eq10 eq57276
    | exact resolve eq57276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57276
  have eq57303 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq57292
    | exact resolve eq57292 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57292
  have eq57311 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ y)) := by
    first
    | exact superpose eq54625 eq57303
    | exact resolve eq57303 eq54625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57303
  have eq57317 : (σ (σ (k (M.op x y) (M.op x y)))) = (σ (σ x)) := by
    first
    | exact superpose eq55952 eq57311
    | exact resolve eq57311 eq55952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57311
  have eq57322 : (σ (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (σ x)) := by
    first
    | exact superpose eq41 eq57317
    | exact resolve eq57317 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq57317
  have eq57325 : (σ (σ x)) = (σ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq54625 eq57322
    | exact resolve eq57322 eq54625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57322
  have eq57328 : (σ (σ x)) = (σ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq55952 eq57325
    | exact resolve eq57325 eq55952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57325
  have eq57329 : (σ (σ x)) = (σ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq20 eq57328
    | exact resolve eq57328 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq57328
  have eq57330 : (σ (σ x)) = (σ (k (σ y) (σ x))) := by
    first
    | exact superpose eq54625 eq57329
    | exact resolve eq57329 eq54625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54625 eq57329
  have eq57331 : (σ (σ x)) = (σ (k (σ x) (σ x))) := by
    first
    | exact superpose eq55952 eq57330
    | exact resolve eq57330 eq55952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55952 eq57330
  have eq57332 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56609 eq57331
    | exact resolve eq57331 eq56609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56609 eq57331
  have eq57435 : (M.op (σ x) (σ y)) = (τ (σ (σ x))) := by
    first
    | exact superpose eq57332 eq15
    | exact resolve eq15 eq57332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57332
  have eq57590 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57435
       have i₂ := eq15 sF2
       grind)
    | exact superpose eq15 eq57435
    | exact resolve eq57435 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57435
  have eq57657 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq57590 eq27
    | exact resolve eq27 eq57590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57590
  have eq57770 : False := by grind
  exact eq57770

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_x_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X2 X1) (M.op X2 X0)) X3) X1) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X2 X1) (M.op X2 X0)) X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X0)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq64 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq23 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op X2 X2) X0) X2) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 (M.op X2 X2) X2 X1
       have i₂ := eq64 X2
       grind)
    | exact superpose eq64 eq23
    | exact resolve eq23 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq83 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq125 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq166 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X3 X0) (M.op X3 X2)) X1)) X4)) X5) X0) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X4 X0 (M.op X0 (M.op (M.op (M.op X3 X0) (M.op X3 X2)) X1)) X5
       have i₂ := eq23 X0 X3 X2 X1
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24
  have eq320 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq324 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq320 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq320 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq320 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq320 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq324 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq324
    | (have j0 := eq324 (σ X0) (σ X1)
       grind)
    | exact resolve eq324 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq324 (τ X0) X1
       grind)
    | exact superpose eq324 eq17
    | (have j1 := eq324 (τ X0) X1
       grind)
    | exact resolve eq17 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq628 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X1 X0) X2 X1
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq902 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
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
  have eq941 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq902 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq902
    | (have j0 := eq902 X0 X1
       grind)
    | exact resolve eq902 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq1730 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq58 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1848 : ∀ X0 X1 : G, (σ X1) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq325 X0 X1
       grind)
    | exact superpose eq325 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq325 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq325 X0 X1
       grind)
    | exact resolve eq12 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq1874 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1848 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1886 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1874 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1874
    | (have j0 := eq1874 X0 X1
       grind)
    | exact resolve eq1874 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1899 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1886 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1886
    | exact resolve eq1886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1886 x y
       grind)
    | exact superpose eq1886 eq16
    | (have j1 := eq1886 x y
       grind)
    | exact resolve eq16 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1970 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1899 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1899
    | (have j0 := eq1899 X0 X1
       grind)
    | exact resolve eq1899 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899
  have eq1972 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1970 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1970
    | (have j0 := eq1970 X0 X1
       grind)
    | exact resolve eq1970 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1970
  have eq2090 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1972 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1972
    | exact resolve eq1972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq2133 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2090 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2159 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 (M.op X0 X1)
       have i₂ := eq125 X1 X0
       grind)
    | exact superpose eq125 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1917
       have i₂ := eq941 x y
       grind)
    | exact superpose eq941 eq1917
    | (have j1 := eq941 x y
       grind)
    | (have r₁ := eq1917
       have r₂ := eq941 x y
       grind)
    | exact resolve eq1917 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq1917
  have eq2348 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq2347
  have eq2352 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq2348
       grind)
    | exact superpose eq2348 eq10
    | exact resolve eq10 eq2348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2401 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2352
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2352
    | exact resolve eq2352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2402 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq2401
       grind)
    | exact superpose eq2401 eq9
    | exact resolve eq9 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2422 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq125 x y
       have i₂ := eq2401
       grind)
    | exact superpose eq2401 eq125
    | exact resolve eq125 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2430 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq628 x y x
       have i₂ := eq2401
       grind)
    | exact superpose eq2401 eq628
    | exact resolve eq628 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2440 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2430 X0
       have i₂ := eq125 X0 y
       grind)
    | exact superpose eq125 eq2430
    | exact resolve eq2430 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2448 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2402 X0
       have i₂ := eq125 X0 y
       grind)
    | exact superpose eq125 eq2402
    | exact resolve eq2402 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq2933 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2448 y
       have i₂ := eq2422
       grind)
    | exact superpose eq2422 eq2448
    | exact resolve eq2448 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422 eq2448
  have eq2992 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq2933
  have eq2996 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2401
       have i₂ := eq2992
       grind)
    | exact superpose eq2992 eq2401
    | exact resolve eq2401 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2998 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2440 x
       have i₂ := eq2992
       grind)
    | exact superpose eq2992 eq2440
    | exact resolve eq2440 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440 eq2992
  have eq3036 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2998
  have eq3038 : x = (M.op x y) ∨ x = y := by grind
  clear eq2996
  have eq3371 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq3036
  have eq3373 : x = (M.op x y) := by
    first
    | (have r₁ := eq3371
       have r₂ := eq3038
       grind)
    | exact resolve eq3371 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038 eq3371
  have eq3375 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq3373
       grind)
    | exact superpose eq3373 eq9
    | exact resolve eq9 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3398 : x = (M.op x x) := by
    first
    | (have i₁ := eq125 y x
       have i₂ := eq3373
       grind)
    | exact superpose eq3373 eq125
    | exact resolve eq125 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3408 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq628 y x x
       have i₂ := eq3373
       grind)
    | exact superpose eq3373 eq628
    | exact resolve eq628 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3411 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq2159 x y
       have i₂ := eq3373
       grind)
    | exact superpose eq3373 eq2159
    | (have r₁ := eq2159 x y
       have r₂ := eq3373
       grind)
    | exact resolve eq2159 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159
  have eq3412 : x = (k x x) := by grind
  clear eq3411
  have eq3416 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3408 X0
       have i₂ := eq125 X0 x
       grind)
    | exact superpose eq125 eq3408
    | exact resolve eq3408 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3408
  have eq3428 : ∀ X0 : G, y = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq3375 X0
       have i₂ := eq125 X0 x
       grind)
    | exact superpose eq125 eq3375
    | exact resolve eq3375 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq3375
  have eq3661 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1730 x
       have i₂ := eq3412
       grind)
    | exact superpose eq3412 eq1730
    | (have j0 := eq1730 x
       grind)
    | exact resolve eq1730 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730 eq3412
  have eq3670 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3661
  have eq4295 : y = (M.op x y) := by
    first
    | (have i₁ := eq3428 x
       have i₂ := eq3398
       grind)
    | exact superpose eq3398 eq3428
    | exact resolve eq3428 eq3398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq4307 : ∀ X3 : G, (M.op (M.op (M.op (M.op x y) X3) x) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq166 x x x x y X3
       have i₂ := eq3428 (M.op (M.op (M.op x x) (M.op x x)) x)
       grind)
    | exact superpose eq3428 eq166
    | exact resolve eq166 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq3428
  have eq4361 : ∀ X3 : G, (M.op (M.op (M.op x X3) x) X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq4307 X3
       have i₂ := eq3373
       grind)
    | exact superpose eq3373 eq4307
    | exact resolve eq4307 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4307
  have eq4363 : x = y := by
    first
    | (have i₁ := eq4295
       have i₂ := eq3373
       grind)
    | exact superpose eq3373 eq4295
    | exact resolve eq4295 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373 eq4295
  have eq4365 : ∀ X3 : G, (M.op x X3) = X3 := by
    intro X3
    first
    | (have i₁ := eq4361 X3
       have i₂ := eq3416 X3
       grind)
    | exact superpose eq3416 eq4361
    | exact resolve eq4361 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361
  have eq4397 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3416 X0
       have i₂ := eq4365 X0
       grind)
    | exact superpose eq4365 eq3416
    | exact resolve eq3416 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq4428 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X1 x X0
       have i₂ := eq4365 X0
       grind)
    | exact superpose eq4365 eq628
    | exact resolve eq628 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq4460 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4428 X0 x
       have i₂ := eq4365 x
       grind)
    | (have i₁ := eq4428 X0 X1
       have i₂ := eq4365 (M.op x X1)
       grind)
    | exact superpose eq4365 eq4428
    | exact resolve eq4428 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365 eq4428
  have eq5120 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq3670
       grind)
    | exact superpose eq3670 eq9
    | exact resolve eq9 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq5175 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5120 X0
       have i₂ := eq4460 X0 (σ x)
       grind)
    | exact superpose eq4460 eq5120
    | exact resolve eq5120 eq4460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4460 eq5120
  have eq5190 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5175 (σ y)
       grind)
    | exact superpose eq5175 eq16
    | exact resolve eq16 eq5175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5175
  have eq5241 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5190
       have i₂ := eq4363
       grind)
    | exact superpose eq4363 eq5190
    | exact resolve eq5190 eq4363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363 eq5190
  have eq5244 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5241
       have i₂ := eq4397 x
       grind)
    | exact superpose eq4397 eq5241
    | exact resolve eq5241 eq4397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397 eq5241
  have eq5245 : False := by grind
  exact eq5245
