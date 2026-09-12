import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op x x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq97 X0 X1
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq97 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq97 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq120 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq118 X0 X1
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq118
  have eq162 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq165 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       have j1 := eq120 X1 X0
       grind)
    | (have r₁ := eq162 X1 X0
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq162 X1 X1
       have r₂ := eq120 X1 X1
       grind)
    | exact resolve eq162 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq162
  have eq374 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq165 (σ X1) (σ X0)
       grind)
    | exact superpose eq165 eq15
    | exact resolve eq15 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq165 X1 X0
       grind)
    | exact superpose eq165 eq374
    | exact resolve eq374 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq374
  have eq381 : False := by grind
  exact eq381

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_x_pxy_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq28
    | (have j0 := eq28 (M.op x y)
       grind)
    | exact resolve eq28 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq35 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op y y) = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq159 : ∀ X0 : G, (M.op y y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x X0) (M.op x X0)) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq57 eq12
    | (have j0 := eq12 (M.op x X0) (M.op x y)
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq161 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq163 y
       grind)
    | exact superpose eq163 eq77
    | exact resolve eq77 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq168 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq32
       have i₂ := eq163 sF0
       grind)
    | exact superpose eq163 eq32
    | exact resolve eq32 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq170 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq159 X0
       grind)
    | (have r₁ := eq159 X0
       have r₂ := eq87
       grind)
    | exact resolve eq159 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq172 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq87 eq168
    | exact resolve eq168 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq173 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq167
       have i₂ := eq163 sF3
       grind)
    | exact superpose eq163 eq167
    | exact resolve eq167 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq175 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq170 X0
       have i₂ := eq88 X0 x X0
       grind)
    | (have i₁ := eq170 y
       have i₂ := eq88 y x x
       grind)
    | exact superpose eq88 eq170
    | exact resolve eq170 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq176 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq172
       have i₂ := eq163 sF1
       grind)
    | exact superpose eq163 eq172
    | exact resolve eq172 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq177 : (M.op (M.op x y) (M.op x (σ y))) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq173
       have i₂ := eq54 sF3
       grind)
    | exact superpose eq54 eq173
    | exact resolve eq173 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq179 : (σ (M.op y y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq176
       have i₂ := eq54 sF1
       grind)
    | exact superpose eq54 eq176
    | exact resolve eq176 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq180 : (M.op (M.op x y) (M.op x (σ y))) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq179
       have i₂ := eq177
       grind)
    | exact superpose eq177 eq179
    | exact resolve eq179 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq179
  have eq198 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq163 (σ X0)
       grind)
    | exact superpose eq163 eq15
    | exact resolve eq15 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq198
    | exact resolve eq198 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op x y) (M.op x (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq199 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq199
    | exact resolve eq199 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq209 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq119
    | exact resolve eq119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq240 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq209 X0 X0
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq209
    | exact resolve eq209 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq240 X0
       have i₂ := eq163 (τ X0)
       grind)
    | exact superpose eq163 eq240
    | exact resolve eq240 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq240
  have eq288 : ∀ X0 : G, (M.op (M.op x y) (M.op x (τ X0))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq274
    | exact resolve eq274 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq413 : ∀ X0 : G, (k (τ (M.op x X0)) (τ (M.op x y))) = (τ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq175 eq209
    | exact resolve eq209 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq209
  have eq423 : ∀ X0 : G, (M.op (M.op x y) (M.op x (σ X0))) = (σ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq202 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq202
    | exact resolve eq202 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 : G, (M.op (M.op x y) (M.op x (τ X0))) = (τ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq288
    | exact resolve eq288 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq460 : ∀ X0 : G, (M.op (M.op x y) (M.op x (τ X0))) = (k (τ (M.op x X0)) (τ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq413 eq451
    | exact resolve eq451 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq464 : ∀ X0 : G, (M.op (M.op x y) (M.op x (τ X0))) = (τ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq460 eq413
    | exact resolve eq413 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq460
  have eq486 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq500 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq72
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq500
    | exact resolve eq500 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq517 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x (σ X0))) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq537 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq503
       have i₂ := eq54 sF2
       grind)
    | exact superpose eq54 eq503
    | exact resolve eq503 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq550 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op x y) (M.op x (σ X0))) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op x y) (M.op x (σ X1))) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq54 (σ X1)
       grind)
    | exact superpose eq54 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq568 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq537
    | exact resolve eq537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq591 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq568
       have i₂ := eq54 sF3
       grind)
    | exact superpose eq54 eq568
    | exact resolve eq568 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq597 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | exact superpose eq180 eq591
    | exact resolve eq591 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq600 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq597
    | exact resolve eq597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq917 : ∀ X0 X1 : G, (σ (M.op (M.op x y) (M.op x X0))) = (M.op (M.op x y) (M.op x (σ (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (M.op X1 X0)
       have i₂ := eq88 X0 X1 X0
       grind)
    | (have i₁ := eq202 (M.op x y)
       have i₂ := eq88 y X1 x
       grind)
    | exact superpose eq88 eq202
    | exact resolve eq202 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X2) (M.op X1 X0)
       have i₂ := eq88 X0 X1 X2
       grind)
    | (have i₁ := eq12 (M.op x y) (M.op x X0)
       have i₂ := eq88 X0 X1 X2
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (M.op X1 X2) (M.op X1 X0)
       grind)
    | (have r₁ := eq12 (M.op x X2) (M.op x y)
       have r₂ := eq88 y x X2
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op x X2)
       have r₂ := eq88 X2 x X2
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq922 X0 X1 X2
       grind)
    | (have r₁ := eq922 X0 X1 X2
       have r₂ := eq88 X0 X1 X0
       grind)
    | (have r₁ := eq922 y x X2
       have r₂ := eq88 y x y
       grind)
    | exact resolve eq922 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq925 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x (σ X0))) = (M.op (M.op x y) (M.op x (σ (M.op X1 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq423 eq917
    | exact resolve eq917 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq917
  have eq943 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op x X2)) = (k (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq923 X0 X1 X2
       have i₂ := eq88 X2 X1 X2
       grind)
    | (have i₁ := eq923 X0 x y
       have i₂ := eq88 y X1 X2
       grind)
    | exact superpose eq88 eq923
    | exact resolve eq923 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq923
  have eq1803 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (k (M.op (M.op x y) (M.op x X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq943 X1 X0 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq943
    | exact resolve eq943 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1820 : ∀ X0 : G, (M.op (M.op x y) (M.op x (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq943
    | (have j0 := eq943 X0 (σ x) (σ y)
       grind)
    | exact resolve eq943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1853 : ∀ X0 : G, (M.op (M.op x y) (M.op x (σ (M.op x y)))) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq180 eq1820
    | exact resolve eq1820 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq2017 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (M.op x y) (M.op x (σ X0))) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op x y) (M.op x (σ X1))) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq550
    | (have j0 := eq550 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq550 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8622 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq161 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq161
    | (have j0 := eq161 y x
       grind)
    | exact resolve eq161 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8623 : (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) (M.op x (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq161
    | (have j0 := eq161 (σ y) (σ x)
       grind)
    | exact resolve eq161 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq8640 : (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq180 eq8623
    | exact resolve eq8623 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8623
  have eq8641 : (M.op x y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq87 eq8622
    | exact resolve eq8622 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8622
  have eq8659 : (k (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq8640
       have i₂ := eq54 sF2
       grind)
    | exact superpose eq54 eq8640
    | exact resolve eq8640 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8640
  have eq8676 : (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (σ (k x y)) = (M.op (M.op x y) (M.op x (σ x))) := by
    first
    | exact superpose eq72 eq8659
    | exact resolve eq8659 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq8659
  have eq99332 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2017 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2017
    | (have j0 := eq2017 x y
       grind)
    | exact resolve eq2017 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq99384 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq99332
    | exact resolve eq99332 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99332
  have eq99386 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99384
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99384
    | exact resolve eq99384 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99384
  have eq99387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99386
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99386
    | exact resolve eq99386 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99386
  have eq99388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq99387
    | exact resolve eq99387 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99387
  have eq99389 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq99388
       have r₂ := eq27
       grind)
    | exact resolve eq99388 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99388
  have eq99390 : (M.op (M.op x y) (M.op x (σ x))) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99389
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99389
    | exact resolve eq99389 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99389
  have eq99391 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99390
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99390
    | exact resolve eq99390 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99390
  have eq99392 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq99391
    | exact resolve eq99391 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99391
  have eq99393 : (M.op (M.op x y) (M.op x (σ y))) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99392
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99392
    | exact resolve eq99392 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99392
  have eq99394 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99393
    | exact resolve eq99393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99393
  have eq99395 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq180 eq99394
    | exact resolve eq99394 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99394
  have eq99396 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq99395
    | exact resolve eq99395 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99395
  have eq99423 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq99396 eq1803
    | exact resolve eq1803 eq99396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99396
  have eq99505 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1853 eq99423
    | exact resolve eq99423 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99423
  have eq99506 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq99505
  have eq99536 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq99506 eq8676
    | (have r₁ := eq8676
       have r₂ := eq99506
       grind)
    | exact resolve eq8676 eq99506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8676 eq99506
  have eq99612 : (σ (k x y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq99536
  have eq107520 : (k x y) = (τ (M.op (M.op x y) (M.op x (σ x)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq99612
       grind)
    | exact superpose eq99612 eq10
    | exact resolve eq10 eq99612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99612
  have eq107609 : (k x y) = (M.op (M.op x y) (M.op x (τ (σ x)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq464 eq107520
    | exact resolve eq107520 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq107520
  have eq107646 : (k x y) = (M.op (M.op x y) (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq38 eq107609
    | exact resolve eq107609 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq107609
  have eq107668 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq54 eq107646
    | exact resolve eq107646 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107646
  have eq107689 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq107668
       have r₂ := eq8641
       grind)
    | exact resolve eq107668 eq8641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107668
  have eq107736 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq107689
       grind)
    | exact superpose eq107689 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq107689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107739 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq550 x y
       have i₂ := eq107689
       grind)
    | exact superpose eq107689 eq550
    | (have j0 := eq550 x y
       grind)
    | exact resolve eq550 eq107689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq107689
  have eq107747 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq107736
  have eq107756 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107739
       have i₂ := eq202 x
       grind)
    | exact superpose eq202 eq107739
    | exact resolve eq107739 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107739
  have eq107757 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq107756
  have eq107759 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107747
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107747
    | exact resolve eq107747 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107747
  have eq107760 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq107759
  have eq107774 : (M.op (M.op x y) (M.op x (σ x))) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107757
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq107757
    | exact resolve eq107757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107757
  have eq107775 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107760
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107760
    | exact resolve eq107760 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq107760
  have eq107787 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107774
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq107774
    | exact resolve eq107774 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107774
  have eq107798 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq107787
    | exact resolve eq107787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107787
  have eq107809 : (M.op (M.op x y) (M.op x (σ y))) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107798
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq107798
    | exact resolve eq107798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107798
  have eq107821 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107809
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq107809
    | exact resolve eq107809 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107809
  have eq107836 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq180 eq107821
    | exact resolve eq107821 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107821
  have eq107846 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq107836
    | exact resolve eq107836 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq107836
  have eq107883 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq202 y
       have i₂ := eq107775
       grind)
    | exact superpose eq107775 eq202
    | exact resolve eq202 eq107775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107775
  have eq107978 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107883
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq107883
    | exact resolve eq107883 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq107883
  have eq107984 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq180 eq107978
    | exact resolve eq107978 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq107978
  have eq107986 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq107984
    | exact resolve eq107984 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107984
  have eq1553373 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq107846 eq1803
    | exact resolve eq1803 eq107846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803 eq107846
  have eq1553378 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1853 eq1553373
    | exact resolve eq1553373 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853 eq1553373
  have eq1553379 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1553378
  have eq1553403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1553379 eq107986
    | exact resolve eq107986 eq1553379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107986 eq1553379
  have eq1554178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1553403
  have eq1554202 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1554178
       have r₂ := eq27
       grind)
    | exact resolve eq1554178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554178
  have eq1554235 : (M.op x y) = (k x y) ∨ (M.op x y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq8641
       have i₂ := eq1554202
       grind)
    | exact superpose eq1554202 eq8641
    | exact resolve eq8641 eq1554202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8641
  have eq1554606 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq1554202
       grind)
    | exact superpose eq1554202 eq54
    | exact resolve eq54 eq1554202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1554609 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ x))) := by
    first
    | (have i₁ := eq202 x
       have i₂ := eq1554202
       grind)
    | exact superpose eq1554202 eq202
    | exact resolve eq202 eq1554202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1554702 : (M.op (M.op x y) (M.op x (σ x))) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq925 x x
       have i₂ := eq1554202
       grind)
    | exact superpose eq1554202 eq925
    | exact resolve eq925 eq1554202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq1554202
  have eq1554727 : (M.op (M.op x y) (M.op x (σ (M.op x y)))) = (M.op (M.op x y) (M.op x (σ x))) := by
    first
    | exact superpose eq20 eq1554702
    | exact resolve eq1554702 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554702
  have eq1560424 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ x))) := by
    first
    | (have i₁ := eq1554609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1554609
    | exact resolve eq1554609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554609
  have eq1560425 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq87 eq1554606
    | exact resolve eq1554606 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1554606
  have eq1560605 : (M.op (M.op x y) (M.op x (σ x))) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1554727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1554727
    | exact resolve eq1554727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1554727
  have eq1562531 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ x))) := by
    first
    | exact superpose eq20 eq1560424
    | exact resolve eq1560424 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560424
  have eq1562656 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1554235
       have i₂ := eq1560425
       grind)
    | exact superpose eq1560425 eq1554235
    | (have r₁ := eq1554235
       have r₂ := eq1560425
       grind)
    | exact resolve eq1554235 eq1560425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554235 eq1560425
  have eq1562690 : (M.op x y) = (k x y) := by grind
  clear eq1562656
  have eq1562877 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq1560605 eq600
    | exact resolve eq600 eq1560605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq1563285 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq1562877
  have eq1564288 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq1560605 eq1562531
    | exact resolve eq1562531 eq1560605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560605 eq1562531
  have eq1564338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1563285
       have i₂ := eq1562690
       grind)
    | exact superpose eq1562690 eq1563285
    | exact resolve eq1563285 eq1562690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562690 eq1563285
  have eq1565805 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq1564338
    | exact resolve eq1564338 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1564338
  have eq1566275 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have r₁ := eq1565805
       have r₂ := eq27
       grind)
    | exact resolve eq1565805 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565805
  have eq1566655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1564288 eq1566275
    | exact resolve eq1566275 eq1564288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564288 eq1566275
  have eq1566877 : False := by grind
  exact eq1566877

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq73 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq74 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k y x) := by
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
  have eq92 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq105 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq107 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq121 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq107 eq16
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq99
    | (have j0 := eq99 (σ X0) (σ X1)
       grind)
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq99 y x
       grind)
    | exact superpose eq99 eq105
    | (have j1 := eq99 y x
       grind)
    | exact resolve eq105 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq139 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq137
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq139
    | exact resolve eq139 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq139
  have eq209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq140 eq99
    | (have j0 := eq99 (σ y) (σ x)
       grind)
    | exact resolve eq99 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq209
    | exact resolve eq209 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq213 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq210
       have r₂ := eq27
       grind)
    | exact resolve eq210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq215 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq213
    | exact resolve eq213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq217 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq215 eq27
    | exact resolve eq27 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1120 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq215 eq92
    | (have r₁ := eq92
       have r₂ := eq215
       grind)
    | exact resolve eq92 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq1121 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1120
  have eq1124 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1121 eq140
    | exact resolve eq140 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1128 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1124
  have eq1133 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1128
       have r₂ := eq217
       grind)
    | exact resolve eq1128 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq1128
  have eq1139 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1133 eq74
    | exact resolve eq74 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1133
  have eq1176 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1139
       have r₂ := eq215
       grind)
    | exact resolve eq1139 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq1139
  have eq1908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1176 eq140
    | exact resolve eq140 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq1176
  have eq1911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1908
  have eq1915 : x = (M.op x y) := by
    first
    | (have r₁ := eq1911
       have r₂ := eq27
       grind)
    | exact resolve eq1911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1917 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1915 eq20
    | exact resolve eq20 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1921 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq1915 eq91
    | (have r₁ := eq91
       have r₂ := eq1915
       grind)
    | exact resolve eq91 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1927 : x = (M.op x x) ∨ x = (k y x) := by grind
  clear eq1921
  have eq1933 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1917
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1917
    | exact resolve eq1917 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq2093 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1933 eq26
    | exact resolve eq26 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2300 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq122
    | (have j0 := eq122 X0 (M.op x y)
       grind)
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq122
  have eq2388 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1915 eq2300
    | (have j0 := eq2300 X0
       grind)
    | exact resolve eq2300 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300
  have eq3625 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2388 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2388
    | (have j0 := eq2388 y
       grind)
    | exact resolve eq2388 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2388
  have eq3659 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2093 eq3625
    | exact resolve eq3625 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq3675 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3659
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq3659
    | exact resolve eq3659 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq3659
  have eq3686 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1933 eq3675
    | exact resolve eq3675 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675
  have eq3693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2093 eq3686
    | exact resolve eq3686 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq3686
  have eq3697 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3693
       have r₂ := eq27
       grind)
    | exact resolve eq3693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq3704 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3697 eq121
    | exact resolve eq121 eq3697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq3697
  have eq3706 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1915 eq3704
    | exact resolve eq3704 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq4173 : x = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1927
       have i₂ := eq3706
       grind)
    | exact superpose eq3706 eq1927
    | exact resolve eq1927 eq3706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq4183 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq4173
       grind)
    | exact superpose eq4173 eq73
    | exact resolve eq73 eq4173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4173
  have eq4246 : (M.op x y) = (k y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq4183
       have r₂ := eq1915
       grind)
    | exact resolve eq4183 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183
  have eq4249 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4246
       have i₂ := eq3706
       grind)
    | exact superpose eq3706 eq4246
    | exact resolve eq4246 eq3706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706 eq4246
  have eq4251 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1915 eq4249
    | exact resolve eq4249 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915 eq4249
  have eq4252 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq4251
  have eq4256 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4252 eq15
    | exact resolve eq15 eq4252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4252
  have eq4257 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4256
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4256
    | exact resolve eq4256 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4256
  have eq4258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1933 eq4257
    | exact resolve eq4257 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933 eq4257
  have eq4259 : False := by grind
  exact eq4259

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq50 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq50 (σ X0)
       grind)
    | exact superpose eq50 eq15
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq64
    | exact resolve eq64 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq64
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq88
    | (have j0 := eq88 (σ X0) (σ X1)
       grind)
    | exact resolve eq88 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq10
    | (have j1 := eq89 X0 X1
       grind)
    | exact resolve eq10 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq718 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq755 : x = y ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq718 y x
       grind)
    | exact superpose eq718 eq16
    | (have j1 := eq718 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq718 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq718 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq782 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq16
    | exact resolve eq16 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq783 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have r₁ := eq782
       have r₂ := eq73 x
       grind)
    | exact resolve eq782 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq783
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq783
    | (have j1 := eq88 x y
       grind)
    | (have r₁ := eq783
       have r₂ := eq88 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq783
       have r₂ := eq88 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq783 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq783
  have eq829 : x = y := by grind
  clear eq826
  have eq980 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq829
       grind)
    | exact superpose eq829 eq16
    | exact resolve eq16 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq981 : False := by grind
  exact eq981

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = X2 ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq117 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq213 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op x y) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq380 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq558 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq291
    | exact resolve eq291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq1929 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq73 X0 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq73
    | exact resolve eq73 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq73
  have eq1973 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq1929 X0
       have i₂ := eq14 (M.op x X0) sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq1929
    | exact resolve eq1929 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq1995 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq1973 X0
       have i₂ := eq14 X0 x X0
       grind)
    | exact superpose eq14 eq1973
    | exact resolve eq1973 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq2472 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X1 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq120 X1 X2 X0
       grind)
    | exact superpose eq120 eq14
    | (have j1 := eq120 X1 X2 X0
       grind)
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq17737 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2472 X0 x x
       have i₂ := eq213 x x X0
       grind)
    | (have i₁ := eq2472 x x y
       have i₂ := eq213 X0 x x
       grind)
    | exact superpose eq213 eq2472
    | (have j0 := eq2472 X0 x y
       grind)
    | exact resolve eq2472 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq2472
  have eq17754 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq17737 eq1995
    | (have j1 := eq17737 X0
       grind)
    | exact resolve eq1995 eq17737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995 eq17737
  have eq17808 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17754
  have eq17878 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq17808 (σ X0)
       grind)
    | exact superpose eq17808 eq10
    | exact resolve eq10 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17882 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq558 X0 X0
       have i₂ := eq17808 (τ X0)
       grind)
    | exact superpose eq17808 eq558
    | exact resolve eq558 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq17929 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq17808 sF2
       grind)
    | exact superpose eq17808 eq50
    | exact resolve eq50 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq17961 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq17929
       have i₂ := eq17808 x
       grind)
    | exact superpose eq17808 eq17929
    | exact resolve eq17929 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17929
  have eq18007 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17882 X0
       have i₂ := eq17808 X0
       grind)
    | exact superpose eq17808 eq17882
    | exact resolve eq17882 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17882
  have eq18011 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17878 X0
       have i₂ := eq17808 X0
       grind)
    | exact superpose eq17808 eq17878
    | exact resolve eq17878 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17808 eq17878
  have eq27424 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq380 X0
       have i₂ := eq18007 X0
       grind)
    | exact superpose eq18007 eq380
    | exact resolve eq380 eq18007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq18007
  have eq27425 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq27424 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq27424
    | exact resolve eq27424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27424
  have eq27426 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq27425
  have eq27441 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq27426 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq27426
    | exact resolve eq27426 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27426
  have eq27748 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq27441 X0
       have i₂ := eq18011 X0
       grind)
    | exact superpose eq18011 eq27441
    | exact resolve eq27441 eq18011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18011 eq27441
  have eq27873 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq27748 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq27748
    | exact resolve eq27748 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27748
  have eq93606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq93606
    | exact resolve eq93606 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93606
  have eq93618 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq93607
       have r₂ := eq28
       grind)
    | exact resolve eq93607 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93607
  have eq93622 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq93618
    | exact resolve eq93618 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93618
  have eq93632 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq93622 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq93622
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq93622
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq93622
       grind)
    | exact resolve eq12 eq93622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93622
  have eq93690 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq93632
  have eq93721 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq93690
       have r₂ := eq27
       grind)
    | exact resolve eq93690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93690
  have eq93768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq93721 eq103
    | exact resolve eq103 eq93721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq93721
  have eq93777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq93768
  have eq93780 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq93777
       have r₂ := eq28
       grind)
    | exact resolve eq93777 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93777
  have eq94089 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq93780 eq17961
    | exact resolve eq17961 eq93780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93780
  have eq94350 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq30 eq94089
    | exact resolve eq94089 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94089
  have eq94351 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq94350
  have eq94390 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq94351
       grind)
    | exact superpose eq94351 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq94351
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq94351
       grind)
    | exact resolve eq12 eq94351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94351
  have eq94448 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq94390
  have eq94480 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq94448
       have r₂ := eq19
       grind)
    | exact resolve eq94448 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94448
  have eq94503 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq94480
       grind)
    | exact superpose eq94480 eq80
    | exact resolve eq80 eq94480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq94480
  have eq94523 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq94503
    | exact resolve eq94503 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94503
  have eq94538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94523 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq94523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq94538
    | exact resolve eq94538 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94538
  have eq94552 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq94541
       have r₂ := eq28
       grind)
    | exact resolve eq94541 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94541
  have eq94556 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq94552
    | exact resolve eq94552 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94552
  have eq98035 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94556 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq94556
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq94556
       grind)
    | exact resolve eq12 eq94556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94556
  have eq98093 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq98035
  have eq98124 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq98093
       have r₂ := eq27
       grind)
    | exact resolve eq98093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98093
  have eq98187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98124 eq94523
    | exact resolve eq94523 eq98124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94523 eq98124
  have eq98194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq98187
  have eq98203 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq98194
       have r₂ := eq28
       grind)
    | exact resolve eq98194 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98194
  have eq98211 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98203 eq17961
    | exact resolve eq17961 eq98203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17961 eq98203
  have eq98477 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq98211
    | exact resolve eq98211 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq98211
  have eq98478 : y = (M.op x x) := by grind
  clear eq98477
  have eq98688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27873 x
       have i₂ := eq98478
       grind)
    | exact superpose eq98478 eq27873
    | exact resolve eq27873 eq98478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27873 eq98478
  have eq98793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98688
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq98688
    | exact resolve eq98688 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq98688
  have eq98846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98793
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq98793
    | exact resolve eq98793 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq98793
  have eq98857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq98846
    | exact resolve eq98846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq98846
  have eq98861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98857
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98857
    | exact resolve eq98857 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq98857
  have eq98863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq98861
    | exact resolve eq98861 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq98861
  have eq98865 : False := by grind
  exact eq98865

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ X2 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq9 X0 X0 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = X0 ∨ (M.op X3 X3) = (M.op X0 X3) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq67 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq81 : ∀ X0 X3 : G, (M.op X3 X3) = (M.op X0 X3) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X3
    first
    | (have j0 := eq50 X0 x x X3
       have j1 := eq27 X0 x X0 X3
       grind)
    | (have r₁ := eq50 x X0 x X3
       have r₂ := eq27 X0 x x X3
       grind)
    | exact resolve eq50 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq50
  have eq372 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq376 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq372 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq372 x X0
       have r₂ := eq81 X0 x
       grind)
    | (have r₁ := eq372 x x
       have r₂ := eq81 x x
       grind)
    | exact resolve eq372 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq372
  have eq931 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq376 (σ X1) (σ X0)
       grind)
    | exact superpose eq376 eq15
    | exact resolve eq15 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq931 X0 X1
       have i₂ := eq376 X1 X0
       grind)
    | exact superpose eq376 eq931
    | exact resolve eq931 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq931
  have eq937 : False := by grind
  exact eq937

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq33 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq33 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq56 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq59 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq63 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq74
  have eq362 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq366 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq362 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq362 X1 X1
       have r₂ := eq80 X1 X1
       grind)
    | (have r₁ := eq362 X1 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq362 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq362
  have eq629 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq366 (σ X1) (σ X0)
       grind)
    | exact superpose eq366 eq15
    | exact resolve eq15 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq366 X1 X0
       grind)
    | exact superpose eq366 eq629
    | exact resolve eq629 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq629
  have eq636 : False := by grind
  exact eq636

/-- `Equation3738`: `x ◇ y = (x ◇ z) ◇ (y ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation3738 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3738 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3738.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X3)) := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X5)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 (M.op X1 x) X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 (M.op X0 X3) X4 (M.op X1 x)
       have i₂ := eq14 X0 X1 X3 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq14 X1 X1 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op X2 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq64 X0 x X2 X3 x
       have i₂ := eq14 X2 X0 x x
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq67 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq61 X0 x X2 X3 x
       have i₂ := eq14 X0 X3 x x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq77 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 x)
       have i₂ := eq14 X1 X1 x x
       grind)
    | exact superpose eq14 eq12
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = (k (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X1 X3) (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 X3) (M.op X0 X2)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X2) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = (k (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 X0 X1 X2 X3
       have i₂ := eq14 X0 X0 X2 X2
       grind)
    | exact superpose eq14 eq110
    | (have j0 := eq110 X0 X1 X2 X3
       grind)
    | (have r₁ := eq110 X1 X1 X3 X3
       have r₂ := eq14 X1 X1 X3 X3
       grind)
    | exact resolve eq110 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = (k (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112 X0 X1 X2 X3
       have i₂ := eq14 X0 X0 X2 X2
       grind)
    | exact superpose eq14 eq112
    | (have j0 := eq112 X0 X1 X2 X3
       grind)
    | exact resolve eq112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X2) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 X1 X2 X3
       have i₂ := eq14 X0 X0 X2 X2
       grind)
    | exact superpose eq14 eq113
    | (have j0 := eq113 X0 X1 X2 X3
       grind)
    | exact resolve eq113 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq137 : (σ (k x (k (M.op x y) x))) = (k (σ x) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq35
    | exact resolve eq35 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq205 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq59 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 x y
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X3 : G, (M.op (M.op x y) X1) = (M.op (M.op x X0) (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq211 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq210 x X1 x
       have i₂ := eq14 x X1 x x
       grind)
    | exact superpose eq14 eq210
    | exact resolve eq210 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq218 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq205 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op x x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq218
  have eq229 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X1 X2) (M.op (σ x) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) X0) (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq235 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq234 x X1 x
       have i₂ := eq14 sF2 X1 x x
       grind)
    | exact superpose eq14 eq234
    | exact resolve eq234 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq236 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq233 x x x
       have i₂ := eq14 x sF2 x x
       grind)
    | exact superpose eq14 eq233
    | exact resolve eq233 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq295 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq229 eq12
    | exact resolve eq12 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X2) X0
       have i₂ := eq66 X1 X0 X2
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 x)
       have r₂ := eq66 X0 (M.op X0 x) x
       grind)
    | (have r₁ := eq12 (M.op X0 x) X0
       have r₂ := eq66 X0 X0 x
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq508 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) x)) = (k (k (σ X0) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq39
    | exact resolve eq39 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq545 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq111
    | (have j0 := eq111 (σ X0)
       grind)
    | exact resolve eq111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65
    | (have j0 := eq65 x y X0
       grind)
    | exact resolve eq65 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107 X0 X1 X2
       have i₂ := eq67 X0 X1 X2
       grind)
    | exact superpose eq67 eq107
    | (have j0 := eq107 X0 X1 X2
       grind)
    | (have r₁ := eq107 x X2 x
       have r₂ := eq67 x X2 x
       grind)
    | exact resolve eq107 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq641 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq236 eq639
    | (have j0 := eq639 X0 X1 (σ x)
       grind)
    | (have r₁ := eq639 (σ x) X1 (M.op (σ x) (σ y))
       have r₂ := eq236 (σ x)
       grind)
    | (have r₁ := eq639 (M.op (σ x) (σ y)) X1 (σ x)
       have r₂ := eq236 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq639 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq639
  have eq810 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X0 X2) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq114 X0 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq940 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq77 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq978 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq940 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq979 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq978 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq982 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq979
    | (have j0 := eq979 X0 X1
       grind)
    | exact resolve eq979 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq989 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq511 X2 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq511
    | exact resolve eq511 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1031 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq536 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq536
    | (have j0 := eq536 y X0
       grind)
    | exact resolve eq536 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq536 X1 X0
       have i₂ := eq11 (σ X1) X0
       grind)
    | exact superpose eq11 eq536
    | (have j1 := eq11 (σ X1) X0
       grind)
    | exact resolve eq536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 (M.op X1 X1)
       have i₂ := eq582 (σ X0) X1
       grind)
    | exact superpose eq582 eq536
    | exact resolve eq536 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1053 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1035 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1035
    | exact resolve eq1035 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq2500 : ∀ X0 X1 : G, (k (k X0 (τ X1)) x) = (τ (k (k (σ X0) X1) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (k X0 (τ X1)) x)
       have i₂ := eq540 X0 X1
       grind)
    | exact superpose eq540 eq16
    | exact resolve eq16 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq3997 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq545 X0
       grind)
    | exact superpose eq545 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq545 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq545 X0
       grind)
    | exact resolve eq13 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4000 : ∀ X0 X1 : G, (k X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq582 X1 (σ X0)
       have i₂ := eq545 X0
       grind)
    | exact superpose eq545 eq582
    | (have j1 := eq545 X0
       grind)
    | exact resolve eq582 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4021 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq545 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4035 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3997 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq3997 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq3997 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997
  have eq4461 : ∀ X0 : G, (M.op x x) = (k (M.op x X0) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq810 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq810
    | (have j0 := eq810 x y X0
       grind)
    | exact resolve eq810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq4719 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (k (M.op (σ X0) X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq407 (σ X0) (σ X0) x
       have i₂ := eq545 X0
       grind)
    | exact superpose eq545 eq407
    | (have j0 := eq407 (σ X0) X1 x
       have j1 := eq545 X0
       grind)
    | exact resolve eq407 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4741 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq407 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq4745 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (k (M.op (σ X0) X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4719 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq6548 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (τ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq235 eq508
    | (have j0 := eq508 (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq508 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq6577 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq229 eq6548
    | (have j0 := eq6548 X0
       grind)
    | exact resolve eq6548 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6548
  have eq6586 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) := by
    intro X0
    first
    | exact superpose eq229 eq6577
    | (have j0 := eq6577 X0
       grind)
    | exact resolve eq6577 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6577
  have eq8089 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq982 X0 X1
       have j1 := eq969 X0 X1
       grind)
    | (have r₁ := eq982 X0 X1
       have r₂ := eq969 X0 X1
       grind)
    | (have r₁ := eq982 X1 X1
       have r₂ := eq969 X1 X1
       grind)
    | exact resolve eq982 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq982
  have eq8093 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8089 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8089
    | exact resolve eq8089 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8171 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq8089 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8089
    | (have j0 := eq8089 x X0
       grind)
    | exact resolve eq8089 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8173 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq8089
    | (have j0 := eq8089 (M.op x y) X0
       grind)
    | exact resolve eq8089 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8224 : ∀ X0 : G, (σ (k (k x x) X0)) = (M.op (σ X0) (k (σ x) (σ x))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8089 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq8089
    | (have j0 := eq8089 X0 x
       grind)
    | exact resolve eq8089 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq8255 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8089 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8089
    | (have j0 := eq8089 X0 x
       grind)
    | exact resolve eq8089 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8089
  have eq8315 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8093 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq8093
    | (have j0 := eq8093 X0 X1
       grind)
    | exact resolve eq8093 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8093
  have eq18343 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4741 (σ X0) (σ X0)
       have i₂ := eq545 X0
       grind)
    | exact superpose eq545 eq4741
    | (have j0 := eq4741 (σ X0) x
       have j1 := eq545 X0
       grind)
    | exact resolve eq4741 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq18462 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18343 X0
       have j1 := eq4035 X0 (σ (k X0 X0))
       grind)
    | (have r₁ := eq18343 X0
       have r₂ := eq4035 X0 x
       grind)
    | exact resolve eq18343 eq4035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18343
  have eq18483 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18462 X0
       have j1 := eq13 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq18462 X0
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq18462 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq18487 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq18483 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq18483
    | exact resolve eq18483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18483
  have eq18531 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16 (k (k X0 X0) X0)
       have i₂ := eq18487 X0
       grind)
    | exact superpose eq18487 eq16
    | exact resolve eq16 eq18487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18487
  have eq18650 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18531 X0
       have i₂ := eq16 (k X0 X0)
       grind)
    | exact superpose eq16 eq18531
    | exact resolve eq18531 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18531
  have eq19007 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8171 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8171
    | (have j0 := eq8171 y
       grind)
    | exact resolve eq8171 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq19039 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19007
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq19007
    | exact resolve eq19007 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19007
  have eq19057 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq19039
    | exact resolve eq19039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19039
  have eq19501 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8173 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8173
    | (have j0 := eq8173 y
       grind)
    | exact resolve eq8173 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq19531 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq76 eq19501
    | exact resolve eq19501 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq19501
  have eq19694 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8315 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8315
    | (have j0 := eq8315 X1 X1
       grind)
    | exact resolve eq8315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315
  have eq20426 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq19694 y x
       grind)
    | exact superpose eq19694 eq74
    | (have j1 := eq19694 x x
       grind)
    | exact resolve eq74 eq19694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq20840 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20426
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20426
    | exact resolve eq20426 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20426
  have eq20945 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq20840
    | exact resolve eq20840 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20840
  have eq21004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20945 eq19057
    | exact resolve eq19057 eq20945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19057 eq20945
  have eq21011 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21004
       have r₂ := eq27
       grind)
    | exact resolve eq21004 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21004
  have eq21046 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21011 eq1053
    | exact resolve eq1053 eq21011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21011
  have eq21074 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq21046
    | exact resolve eq21046 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046
  have eq21075 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq21074 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq21074 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq21074 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21074
  have eq21140 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4035 x X0
       have i₂ := eq21075 x
       grind)
    | exact superpose eq21075 eq4035
    | (have j0 := eq4035 x X0
       grind)
    | exact resolve eq4035 eq21075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq21141 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq111 x
       have i₂ := eq21075 x
       grind)
    | exact superpose eq21075 eq111
    | (have j0 := eq111 x
       grind)
    | exact resolve eq111 eq21075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21165 : x = (M.op x x) := by grind
  clear eq21141
  have eq21166 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq21140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21140
  have eq21186 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21166 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21166
    | (have j0 := eq21166 X0
       grind)
    | exact resolve eq21166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21166
  have eq21252 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq564 X0
       have i₂ := eq21165
       grind)
    | exact superpose eq21165 eq564
    | (have j0 := eq564 X0
       grind)
    | exact resolve eq564 eq21165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq21256 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4461 x
       have i₂ := eq21165
       grind)
    | exact superpose eq21165 eq4461
    | exact resolve eq4461 eq21165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461
  have eq21724 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21186 eq111
    | (have j0 := eq111 (σ x)
       grind)
    | exact resolve eq111 eq21186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21748 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21724
  have eq24673 : x = (k x (M.op x y)) := by
    first
    | (have j1 := eq21252 x
       grind)
    | (have r₁ := eq21256
       have r₂ := eq21252 x
       grind)
    | exact resolve eq21256 eq21252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21256
  have eq24677 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq24673 eq45
    | exact resolve eq45 eq24673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq24673
  have eq24701 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq24677
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24677
    | exact resolve eq24677 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24677
  have eq25599 : ∀ X0 X1 : G, (τ (k (σ X0) (σ x))) = (k (k X0 (τ (σ (k X1 X1)))) x) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2500 X0 (σ (k X1 X1))
       have i₂ := eq4000 X1 (σ X0)
       grind)
    | exact superpose eq4000 eq2500
    | (have j1 := eq4000 X1 X1
       grind)
    | exact resolve eq2500 eq4000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500 eq4000
  have eq25610 : ∀ X0 X1 : G, (τ (k (σ X0) (σ x))) = (k X0 (τ (σ (k X1 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25599 X0 X1
       have i₂ := eq21075 (k X0 (τ (σ (k X1 X1))))
       grind)
    | exact superpose eq21075 eq25599
    | (have j0 := eq25599 X0 X1
       grind)
    | exact resolve eq25599 eq21075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25599
  have eq25667 : ∀ X0 X1 : G, (τ (k (σ X0) (σ x))) = (k X0 (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25610 X0 X1
       have i₂ := eq16 (k X1 X1)
       grind)
    | exact superpose eq16 eq25610
    | (have j0 := eq25610 X0 X1
       grind)
    | exact resolve eq25610 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25610
  have eq25708 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = (k X0 (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25667 X0 X1
       have i₂ := eq536 X0 sF2
       grind)
    | exact superpose eq536 eq25667
    | (have j0 := eq25667 X0 X1
       grind)
    | exact resolve eq25667 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25667
  have eq25713 : ∀ X0 X1 : G, (k X0 x) = (k X0 (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq25708
    | (have j0 := eq25708 X0 X1
       grind)
    | exact resolve eq25708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25708
  have eq25715 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25713 X0 X1
       have i₂ := eq21075 X0
       grind)
    | exact superpose eq21075 eq25713
    | (have j0 := eq25713 X0 X1
       grind)
    | exact resolve eq25713 eq21075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25713
  have eq27156 : (σ (k x (k (M.op x y) x))) = (M.op (k (σ (M.op x y)) (σ x)) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq8255
    | exact resolve eq8255 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq8255
  have eq27185 : (M.op (σ (M.op x y)) (σ x)) = (σ (k x (k (M.op x y) x))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq21186 eq27156
    | exact resolve eq27156 eq21186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27156
  have eq27232 : (M.op (σ (M.op x y)) (σ x)) = (k (σ x) (k (σ (M.op x y)) (σ x))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq137 eq27185
    | exact resolve eq27185 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq27185
  have eq27273 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq21186 eq27232
    | exact resolve eq27232 eq21186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27232
  have eq27311 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq24701 eq27273
    | exact resolve eq27273 eq24701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24701 eq27273
  have eq27348 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21186 eq27311
    | exact resolve eq27311 eq21186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27311
  have eq27394 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27348 eq67
    | exact resolve eq67 eq27348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27348
  have eq50330 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq27394
    | (have j0 := eq27394 (σ y)
       grind)
    | exact resolve eq27394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27394
  have eq81901 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq235 eq295
    | (have j0 := eq295 X0
       grind)
    | (have r₁ := eq295 (σ x)
       have r₂ := eq235 (σ x)
       grind)
    | exact resolve eq295 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq81902 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq21748 eq81901
    | (have j0 := eq81901 X0
       grind)
    | exact resolve eq81901 eq21748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81901
  have eq81903 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq21748 eq81902
    | (have j0 := eq81902 X0
       grind)
    | (have r₁ := eq81902 (σ x)
       have r₂ := eq21748
       grind)
    | exact resolve eq81902 eq21748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81902
  have eq81904 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq21748 eq81903
    | (have j0 := eq81903 X0
       grind)
    | (have r₁ := eq81903 (σ x)
       have r₂ := eq21748
       grind)
    | exact resolve eq81903 eq21748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81903
  have eq142311 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq211 eq101
    | exact resolve eq101 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq142312 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq142311
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq142311
    | exact resolve eq142311 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142311
  have eq142313 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq142312
    | exact resolve eq142312 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142312
  have eq142314 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq211 eq142313
    | exact resolve eq142313 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq142313
  have eq142315 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq205 eq142314
    | exact resolve eq142314 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142314
  have eq142316 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq142315
       have i₂ := eq21165
       grind)
    | exact superpose eq21165 eq142315
    | exact resolve eq142315 eq21165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142315
  have eq142317 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq142316
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq142316
    | exact resolve eq142316 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142316
  have eq142318 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq205 eq142317
    | exact resolve eq142317 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq142317
  have eq142319 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142318
       have i₂ := eq21165
       grind)
    | exact superpose eq21165 eq142318
    | exact resolve eq142318 eq21165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142318
  have eq142320 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq142319
  have eq142321 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19531 eq142320
    | exact resolve eq142320 eq19531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19531 eq142320
  have eq147823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq142321 eq50330
    | exact resolve eq50330 eq142321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50330 eq142321
  have eq147847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq147823
  have eq147849 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq147847
       have r₂ := eq27
       grind)
    | exact resolve eq147847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147847
  have eq147868 : ∀ X0 : G, (k X0 (τ (σ (M.op x y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147849 eq1053
    | exact resolve eq1053 eq147849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147849
  have eq147893 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq147868
    | exact resolve eq147868 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147868
  have eq147896 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq147893 X0
       have j1 := eq21252 X0
       grind)
    | (have r₁ := eq147893 X0
       have r₂ := eq21252 X0
       grind)
    | exact resolve eq147893 eq21252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21252 eq147893
  have eq148020 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq147896 eq221
    | exact resolve eq221 eq147896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq148093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq147896 eq4021
    | (have j0 := eq4021 (M.op x y)
       grind)
    | exact resolve eq4021 eq147896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147896
  have eq148190 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq148093
  have eq148193 : (M.op x y) = (M.op x x) := by grind
  clear eq148020
  have eq148284 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq148190
    | exact resolve eq148190 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148190
  have eq148315 : x = (M.op x y) := by
    first
    | (have i₁ := eq148193
       have i₂ := eq21165
       grind)
    | exact superpose eq21165 eq148193
    | exact resolve eq148193 eq21165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21165 eq148193
  have eq149937 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq148315 eq20
    | exact resolve eq20 eq148315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq150242 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq149937
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq149937
    | exact resolve eq149937 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149937
  have eq150372 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq150242 eq26
    | exact resolve eq26 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq150551 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq150242 eq81904
    | exact resolve eq81904 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81904
  have eq150575 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq150551 X0
       grind)
    | (have r₁ := eq150551 X0
       have r₂ := eq27
       grind)
    | exact resolve eq150551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150551
  have eq151364 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (k X1 (M.op (σ (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq148284 eq65
    | (have j0 := eq65 (σ (M.op x y)) X0 X1
       grind)
    | exact resolve eq65 eq148284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq163497 : ∀ X0 : G, (σ (k (k x x) X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21186 eq8224
    | (have j0 := eq8224 X0
       grind)
    | exact resolve eq8224 eq21186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8224 eq21186
  have eq163498 : ∀ X0 : G, (σ (k (k x x) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq150242 eq163497
    | (have j0 := eq163497 X0
       grind)
    | exact resolve eq163497 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163497
  have eq163499 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq163498 X0
       have i₂ := eq21075 x
       grind)
    | exact superpose eq21075 eq163498
    | (have j0 := eq163498 X0
       grind)
    | exact resolve eq163498 eq21075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21075 eq163498
  have eq170470 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ (M.op x y))) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq150242 eq641
    | (have j0 := eq641 X0 X1
       grind)
    | exact resolve eq641 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq170520 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have j0 := eq170470 (σ (M.op x y)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170470
  have eq170534 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq148284 eq170520
    | (have j0 := eq170520 X0
       grind)
    | exact resolve eq170520 eq148284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170520
  have eq170549 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq148284 eq170534
    | (have j0 := eq170534 X0
       grind)
    | exact resolve eq170534 eq148284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170534
  have eq171454 : ∀ X0 : G, (τ (M.op (σ x) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq235 eq1034
    | (have j0 := eq1034 (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq1034 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq1034
  have eq171754 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq150242 eq171454
    | (have j0 := eq171454 X0
       grind)
    | exact resolve eq171454 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171454
  have eq171979 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq229 eq171754
    | (have j0 := eq171754 X0
       grind)
    | exact resolve eq171754 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171754
  have eq172131 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq150242 eq171979
    | (have j0 := eq171979 X0
       grind)
    | exact resolve eq171979 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171979
  have eq172247 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq148284 eq172131
    | (have j0 := eq172131 X0
       grind)
    | exact resolve eq172131 eq148284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172131
  have eq172342 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq229 eq172247
    | (have j0 := eq172247 X0
       grind)
    | exact resolve eq172247 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq172247
  have eq172392 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq21748 eq172342
    | (have j0 := eq172342 X0
       grind)
    | exact resolve eq172342 eq21748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172342
  have eq172441 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq150242 eq172392
    | (have j0 := eq172392 X0
       grind)
    | exact resolve eq172392 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172392
  have eq172485 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ X0))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq172441 X0
       grind)
    | (have r₁ := eq172441 X0
       have r₂ := eq27
       grind)
    | exact resolve eq172441 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172441
  have eq179058 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) := by
    intro X0
    first
    | exact superpose eq21748 eq6586
    | (have j0 := eq6586 X0
       grind)
    | exact resolve eq6586 eq21748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586 eq21748
  have eq179059 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) := by
    intro X0
    first
    | exact superpose eq150242 eq179058
    | (have j0 := eq179058 X0
       grind)
    | exact resolve eq179058 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179058
  have eq179060 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq179059 X0
       grind)
    | (have r₁ := eq179059 X0
       have r₂ := eq27
       grind)
    | exact resolve eq179059 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179059
  have eq179061 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (τ X0)) ∨ (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) := by
    intro X0
    first
    | exact superpose eq150242 eq179060
    | (have j0 := eq179060 X0
       grind)
    | exact resolve eq179060 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179060
  have eq179062 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (τ X0)) ∨ (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ x) (τ X0))) := by
    intro X0
    first
    | exact superpose eq148284 eq179061
    | (have j0 := eq179061 X0
       grind)
    | exact resolve eq179061 eq148284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148284 eq179061
  have eq179063 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (σ (M.op x y)) (τ X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq150242 eq179062
    | (have j0 := eq179062 X0
       grind)
    | exact resolve eq179062 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179062
  have eq179069 : ∀ X0 : G, (σ (M.op (σ (M.op x y)) X0)) = (k (σ X0) (σ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq179063 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq179063
    | exact resolve eq179063 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179063
  have eq179490 : ∀ X0 : G, (σ (M.op (σ (M.op x y)) X0)) = (σ (k X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq179069 X0
       have i₂ := eq10 X0 sF4
       grind)
    | exact superpose eq10 eq179069
    | (have j0 := eq179069 X0
       grind)
    | exact resolve eq179069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179069
  have eq213176 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (τ (σ (M.op (σ (M.op x y)) X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq179490 eq16
    | (have j1 := eq179490 X0
       grind)
    | exact resolve eq16 eq179490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179490
  have eq213410 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq213176 X0
       have i₂ := eq16 (M.op sF1 X0)
       grind)
    | exact superpose eq16 eq213176
    | (have j0 := eq213176 X0
       grind)
    | exact resolve eq213176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213176
  have eq257233 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k (M.op (σ X0) X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4745 X0 X1
       have j1 := eq4021 X0
       grind)
    | (have r₁ := eq4745 X0 X1
       have r₂ := eq4021 X0
       grind)
    | exact resolve eq4745 eq4021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021 eq4745
  have eq257248 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k x X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq163499 eq257233
    | (have j0 := eq257233 X0 x
       have j1 := eq163499 X0
       grind)
    | exact resolve eq257233 eq163499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163499 eq257233
  have eq257645 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k x X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq257248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257248
  have eq257862 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k x X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq257645 X0
       have i₂ := eq10 (k x X0) X0
       grind)
    | exact superpose eq10 eq257645
    | (have j0 := eq257645 X0
       grind)
    | exact resolve eq257645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257645
  have eq309476 : ∀ X0 X1 X2 : G, (k X1 (τ (σ X0))) = X1 ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1053 X1 (σ X0)
       have i₂ := eq25715 X2 X0
       grind)
    | exact superpose eq25715 eq1053
    | (have j1 := eq25715 X2 X0
       grind)
    | exact resolve eq1053 eq25715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq25715
  have eq309507 : ∀ X0 X1 X2 : G, (k X2 (k X0 X0)) = X2 ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq309476 X0 X1 X2
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq309476
    | (have j0 := eq309476 X0 X1 X2
       grind)
    | exact resolve eq309476 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309476
  have eq310118 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq111 (k X0 X0)
       have i₂ := eq309507 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq309507 eq111
    | (have j0 := eq111 (k X0 X0)
       have j1 := eq309507 X0 X1 x
       grind)
    | exact resolve eq111 eq309507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq309507
  have eq310275 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq310118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310118
  have eq970738 : (τ (M.op (σ (M.op x y)) (σ y))) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq172485 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq172485
    | (have j0 := eq172485 y
       grind)
    | exact resolve eq172485 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq172485
  have eq971244 : (τ (M.op (σ (M.op x y)) (σ y))) = (τ (k (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq970738
       have i₂ := eq1031 sF4
       grind)
    | exact superpose eq1031 eq970738
    | exact resolve eq970738 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970738
  have eq971542 : (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq150372 eq971244
    | exact resolve eq971244 eq150372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971244
  have eq971773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq150372 eq971542
    | exact resolve eq971542 eq150372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150372 eq971542
  have eq971935 : (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq971773
       have r₂ := eq27
       grind)
    | exact resolve eq971773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971773
  have eq1184867 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k x (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (k x (τ X0))
       have i₂ := eq257862 (τ X0)
       grind)
    | exact superpose eq257862 eq38
    | (have j1 := eq257862 (τ X0)
       grind)
    | exact resolve eq38 eq257862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257862
  have eq1185387 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1184867 X0
       have i₂ := eq38 X0 x
       grind)
    | exact superpose eq38 eq1184867
    | (have j0 := eq1184867 X0
       grind)
    | exact resolve eq1184867 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1184867
  have eq1185874 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1185387 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1185387
    | (have j0 := eq1185387 X0
       grind)
    | exact resolve eq1185387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185387
  have eq1186258 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (k (σ (M.op x y)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq150242 eq1185874
    | (have j0 := eq1185874 X0
       grind)
    | exact resolve eq1185874 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185874
  have eq1186571 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k (σ (M.op x y)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1186258 X0
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1186258
    | (have j0 := eq1186258 X0
       grind)
    | exact resolve eq1186258 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1186258
  have eq1186836 : ∀ X0 : G, (k X0 X0) = (k (k (σ (M.op x y)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1186571 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1186571
    | (have j0 := eq1186571 X0
       grind)
    | exact resolve eq1186571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186571
  have eq1187072 : ∀ X0 : G, (k X0 X0) = (k (k (σ (M.op x y)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1186836 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1186836
    | (have j0 := eq1186836 X0
       grind)
    | exact resolve eq1186836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186836
  have eq1188377 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (σ (M.op x y)) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1187072 eq19694
    | (have j0 := eq19694 X0 X0
       have j1 := eq1187072 X0
       grind)
    | exact resolve eq19694 eq1187072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19694 eq1187072
  have eq1189047 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (σ (M.op x y)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1188377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188377
  have eq1192194 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1189047 eq67
    | (have j1 := eq1189047 X0
       grind)
    | exact resolve eq67 eq1189047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189047
  have eq2140919 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1192194 X0 (k X0 X0)
       have i₂ := eq310275 X0 X1
       grind)
    | exact superpose eq310275 eq1192194
    | (have j0 := eq1192194 X0 X1
       have j1 := eq310275 X0 X1
       grind)
    | exact resolve eq1192194 eq310275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310275 eq1192194
  have eq2140990 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2140919 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq2140919 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq2140919 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140919
  have eq2142375 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4741 X0 (k X0 X0)
       have i₂ := eq2140990 X0 X1
       grind)
    | exact superpose eq2140990 eq4741
    | (have j0 := eq4741 X0 X1
       have j1 := eq2140990 X0 X1
       grind)
    | exact resolve eq4741 eq2140990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741 eq2140990
  have eq2142744 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2142375 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq2142375 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq2142375 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142375
  have eq2142818 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2142744 X0 X1
       have i₂ := eq18650 X0
       grind)
    | exact superpose eq18650 eq2142744
    | (have j0 := eq2142744 X0 X1
       grind)
    | exact resolve eq2142744 eq18650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142744
  have eq2143318 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18650 X0
       have i₂ := eq2142818 X0 X1
       grind)
    | exact superpose eq2142818 eq18650
    | (have j1 := eq2142818 X0 (M.op X0 X0)
       grind)
    | exact resolve eq18650 eq2142818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18650 eq2142818
  have eq2157763 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq2143318 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143318
  have eq2157764 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq2157763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157763
  have eq2158781 : ∀ X0 X1 : G, (k (τ X1) (M.op (τ X0) (τ X0))) = (τ (k X1 (k (σ (M.op (τ X0) (τ X0))) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq989 (M.op (τ X0) (τ X0)) X0 X1
       have i₂ := eq2157764 (τ X0)
       grind)
    | exact superpose eq2157764 eq989
    | exact resolve eq989 eq2157764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq2159584 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 (k (σ (M.op (τ X0) (τ X0))) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2158781 X0 X1
       have i₂ := eq582 (τ X1) (τ X0)
       grind)
    | exact superpose eq582 eq2158781
    | exact resolve eq2158781 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq2158781
  have eq2532513 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (k (σ (M.op (τ X1) (τ X1))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (k (σ (M.op (τ X1) (τ X1))) X1))
       have i₂ := eq2159584 X1 X0
       grind)
    | exact superpose eq2159584 eq15
    | exact resolve eq15 eq2159584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159584
  have eq2533401 : ∀ X0 X1 : G, (k X0 (k (σ (M.op (τ X1) (τ X1))) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2532513 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2532513
    | exact resolve eq2532513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532513
  have eq2536484 : ∀ X0 : G, (k X0 (M.op (σ (M.op x y)) (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq213410 eq2533401
    | (have j1 := eq213410 (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))
       grind)
    | exact resolve eq2533401 eq213410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213410 eq2533401
  have eq2538191 : ∀ X0 : G, (k X0 (M.op (σ (M.op x y)) (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))))) = X0 := by
    intro X0
    first
    | (have j0 := eq2536484 X0
       have j1 := eq151364 (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) X0
       grind)
    | (have r₁ := eq2536484 X0
       have r₂ := eq151364 (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) x
       grind)
    | exact resolve eq2536484 eq151364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151364 eq2536484
  have eq2540267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq2538191 eq170549
    | (have j0 := eq170549 (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))
       grind)
    | exact resolve eq170549 eq2538191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170549 eq2538191
  have eq2541586 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))) := by
    first
    | (have r₁ := eq2540267
       have r₂ := eq27
       grind)
    | exact resolve eq2540267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540267
  have eq2542352 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2541586 eq150575
    | (have j0 := eq150575 (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))
       grind)
    | (have r₁ := eq150575 (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))
       have r₂ := eq2541586
       grind)
    | exact resolve eq150575 eq2541586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150575 eq2541586
  have eq2542412 : (σ (M.op x y)) = (k (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) (M.op (σ x) (σ y))) := by grind
  clear eq2542352
  have eq2542470 : (τ (σ (M.op x y))) = (k (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2542412 eq536
    | exact resolve eq536 eq2542412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq2542412
  have eq2542599 : (τ (σ (M.op x y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2542470
       have i₂ := eq2157764 (τ sF4)
       grind)
    | exact superpose eq2157764 eq2542470
    | exact resolve eq2542470 eq2157764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157764 eq2542470
  have eq2542653 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq30 eq2542599
    | exact resolve eq2542599 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2542599
  have eq2542696 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq148315 eq2542653
    | exact resolve eq2542653 eq148315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542653
  have eq2542802 : ∀ X0 : G, (M.op x X0) = (M.op (τ (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2542696 eq67
    | exact resolve eq67 eq2542696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq2544275 : ∀ X0 : G, (M.op x X0) ≠ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2542802 eq12
    | (have j0 := eq12 X0 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq12 eq2542802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542802
  have eq2544553 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2542696 eq2544275
    | (have j0 := eq2544275 X0
       grind)
    | exact resolve eq2544275 eq2542696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544275
  have eq2544753 : ∀ X0 : G, x = (τ (M.op (σ x) (σ y))) ∨ x ≠ (M.op x X0) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2542696 eq2544553
    | (have j0 := eq2544553 X0
       grind)
    | exact resolve eq2544553 eq2542696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544553
  have eq2544882 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2542696 eq2544753
    | (have j0 := eq2544753 X0
       grind)
    | exact resolve eq2544753 eq2542696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542696 eq2544753
  have eq4053321 : x ≠ (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2544882 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2544882
    | (have j0 := eq2544882 y
       grind)
    | exact resolve eq2544882 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2544882
  have eq4053390 : x = (τ (M.op (σ x) (σ y))) ∨ x = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq4053321
       have r₂ := eq148315
       grind)
    | exact resolve eq4053321 eq148315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148315 eq4053321
  have eq4053399 : x = (τ (k (σ y) (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4053390
       have i₂ := eq1031 sF4
       grind)
    | exact superpose eq1031 eq4053390
    | exact resolve eq4053390 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq4053390
  have eq4053406 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq971935 eq4053399
    | exact resolve eq4053399 eq971935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971935 eq4053399
  have eq4053407 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq4053406
  have eq4053491 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4053407 eq15
    | exact resolve eq15 eq4053407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4053407
  have eq4054681 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4053491
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4053491
    | exact resolve eq4053491 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4053491
  have eq4055010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq150242 eq4054681
    | exact resolve eq4054681 eq150242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150242 eq4054681
  have eq4055216 : False := by grind
  exact eq4055216
