import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X1 X0
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
    | (have r₁ := eq102 X1 X1
       have r₂ := eq51 X1 X1
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

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  clear eq24
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) X0) x) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq77 y x
       grind)
    | exact superpose eq77 eq100
    | (have j1 := eq77 y x
       grind)
    | exact resolve eq100 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq116
  have eq138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117 eq77
    | (have j0 := eq77 (σ y) (σ x)
       grind)
    | exact resolve eq77 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq138
    | exact resolve eq138 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq142 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq139
       have r₂ := eq27
       grind)
    | exact resolve eq139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq144 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq142
    | exact resolve eq142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq250 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq261 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq144 eq51
    | exact resolve eq51 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq144
  have eq281 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261 eq14
    | exact resolve eq14 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq291 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq281 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq291 X0
       have j1 := eq77 X0 (σ x)
       grind)
    | (have r₁ := eq291 X0
       have r₂ := eq77 X0 (σ x)
       grind)
    | exact resolve eq291 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq294 eq117
    | exact resolve eq117 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq294
  have eq399 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq396
  have eq402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq399
    | exact resolve eq399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq405 : x = (M.op x y) := by
    first
    | (have r₁ := eq402
       have r₂ := eq27
       grind)
    | exact resolve eq402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq407 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq405 eq20
    | exact resolve eq20 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq414 : x = (M.op x x) := by
    first
    | exact superpose eq405 eq250
    | exact resolve eq250 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq420 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq407
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq407
    | exact resolve eq407 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq423 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq405 eq64
    | exact resolve eq64 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq424 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq405 eq423
    | exact resolve eq423 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq423
  have eq425 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq420 eq26
    | exact resolve eq26 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq475 : x = (k y x) := by
    first
    | (have r₁ := eq424
       have r₂ := eq414
       grind)
    | exact resolve eq424 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq424
  have eq479 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq475
       grind)
    | exact superpose eq475 eq100
    | exact resolve eq100 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq475
  have eq486 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq420 eq479
    | exact resolve eq479 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq488 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq486
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq486
    | exact resolve eq486 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq486
  have eq489 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq420 eq488
    | exact resolve eq488 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq488
  have eq492 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq489 eq77
    | (have j0 := eq77 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq77 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq489
  have eq493 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq492
  have eq495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq425 eq493
    | exact resolve eq493 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq493
  have eq498 : False := by grind
  exact eq498

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq783 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq420 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq420
    | exact resolve eq420 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq799 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq783
    | (have j0 := eq783 X0 X1
       grind)
    | exact resolve eq783 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq783
  have eq808 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq799 X0 X1
       have j1 := eq93 X1 X0
       grind)
    | (have r₁ := eq799 X1 X0
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq799 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq799 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq799
  have eq811 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq808 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq808
    | exact resolve eq808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq808 (σ X1) X0
       grind)
    | exact superpose eq808 eq15
    | (have j1 := eq808 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq863 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq811 (τ X0) X1
       grind)
    | exact superpose eq811 eq19
    | (have j1 := eq811 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq811
  have eq971 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq863 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq863
    | exact resolve eq863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1011 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq971 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq971
    | (have j0 := eq971 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq971 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq1196 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq827 x y
       grind)
    | exact superpose eq827 eq16
    | (have j1 := eq827 x y
       grind)
    | exact resolve eq16 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq1213 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1196
       have i₂ := eq1011 x y
       grind)
    | exact superpose eq1011 eq1196
    | (have j1 := eq1011 (σ x) (σ y)
       grind)
    | (have r₁ := eq1196
       have r₂ := eq1011 x y
       grind)
    | (have r₁ := eq1196
       have r₂ := eq1011 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1196
       have r₂ := eq1011 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1196 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq1196
  have eq1214 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1213
  have eq1217 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1214
       grind)
    | exact superpose eq1214 eq16
    | exact resolve eq16 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1218 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1217
       have r₂ := eq77 x
       grind)
    | exact resolve eq1217 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1219 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1218
       grind)
    | exact superpose eq1218 eq16
    | exact resolve eq16 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1218
       grind)
    | exact superpose eq1218 eq10
    | exact resolve eq10 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1264 : x = y := by
    first
    | (have i₁ := eq1220
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1220
    | exact resolve eq1220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1265 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1219
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq1219
    | exact resolve eq1219 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1219
  have eq1266 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1265
       have i₂ := eq1264
       grind)
    | exact superpose eq1264 eq1265
    | exact resolve eq1265 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq1265
  have eq1267 : False := by grind
  exact eq1267

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq402 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq404 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq432 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq402
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq402
    | exact resolve eq402 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq433 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq428 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq434 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq433 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq433 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq433 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq445 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq434 (σ X0)
       grind)
    | exact superpose eq434 eq15
    | exact resolve eq15 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq434 X0
       grind)
    | exact superpose eq434 eq445
    | exact resolve eq445 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq445
  have eq749 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq431 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq431
    | (have j0 := eq431 (σ X1) (σ X0)
       grind)
    | exact resolve eq431 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq431 (σ X0) X1
       grind)
    | exact superpose eq431 eq22
    | (have j1 := eq431 (σ X0) X1
       grind)
    | exact resolve eq22 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq7345 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq762 X0 X1
       grind)
    | exact superpose eq762 eq22
    | (have j1 := eq762 X0 X1
       grind)
    | exact resolve eq22 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq7357 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq762 X0 (σ X1)
       grind)
    | exact superpose eq762 eq15
    | (have j1 := eq762 X0 (σ X1)
       grind)
    | exact resolve eq15 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq7401 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7357 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7357
    | (have j0 := eq7357 X0 X1
       grind)
    | exact resolve eq7357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7357
  have eq7406 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = X0 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7345 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7345
    | (have j0 := eq7345 X0 X1
       grind)
    | exact resolve eq7345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7345
  have eq7683 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = X1 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq7406 X0 X1
       grind)
    | exact superpose eq7406 eq12
    | (have j1 := eq7406 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq7406 X0 (σ X0)
       grind)
    | exact resolve eq12 eq7406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7684 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = X1 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq7406 X0 X1
       grind)
    | exact superpose eq7406 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq7406 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq7406 X0 X1
       grind)
    | exact resolve eq13 eq7406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7406
  have eq7713 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = X1 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7684 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7684
  have eq7730 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = X1 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7683 X0 X1
       have j1 := eq7713 X0 X1
       grind)
    | (have r₁ := eq7683 (k (σ X1) (σ X1)) X1
       have r₂ := eq7713 (σ X1) X1
       grind)
    | (have r₁ := eq7683 X0 X1
       have r₂ := eq7713 X0 X1
       grind)
    | (have r₁ := eq7683 (σ X1) X1
       have r₂ := eq7713 (σ X1) X1
       grind)
    | exact resolve eq7683 eq7713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7683 eq7713
  have eq8597 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7730 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7730
    | (have j0 := eq7730 X1 (τ X0)
       grind)
    | exact resolve eq7730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8644 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = X1 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq7730 (σ X0) X1
       grind)
    | exact superpose eq7730 eq28
    | (have j1 := eq7730 (σ X0) X1
       grind)
    | exact resolve eq28 eq7730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8645 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ X1))) ∨ (k (τ (τ X0)) X1) = X1 ∨ (k (τ (τ X0)) X1) = (τ (M.op (σ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ X1)
       have i₂ := eq7730 (τ X0) X1
       grind)
    | exact superpose eq7730 eq17
    | (have j1 := eq7730 (τ X0) X1
       grind)
    | exact resolve eq17 eq7730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7730
  have eq8695 : ∀ X0 X1 : G, (k X0 (σ (σ X1))) = X0 ∨ (k (τ (τ X0)) X1) = X1 ∨ (k (τ (τ X0)) X1) = (τ (M.op (σ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8645 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8645
    | (have j0 := eq8645 X0 X1
       grind)
    | exact resolve eq8645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8645
  have eq8696 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = X1 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8644 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8644
    | (have j0 := eq8644 X0 X1
       grind)
    | exact resolve eq8644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq8706 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8597 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8597
    | (have j0 := eq8597 X0 X1
       grind)
    | exact resolve eq8597 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8597
  have eq8728 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = X1 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8696 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8696
    | (have j0 := eq8696 X0 X1
       grind)
    | exact resolve eq8696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8696
  have eq8738 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8706 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8706
    | (have j0 := eq8706 X0 X1
       grind)
    | exact resolve eq8706 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8706
  have eq8741 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8728 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8728
    | (have j0 := eq8728 X0 X1
       grind)
    | exact resolve eq8728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728
  have eq8749 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8741 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8741
    | (have j0 := eq8741 X0 X1
       grind)
    | exact resolve eq8741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8741
  have eq8857 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq8749 X0 X1
       grind)
    | exact superpose eq8749 eq11
    | (have j1 := eq8749 X0 X1
       grind)
    | exact resolve eq11 eq8749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8749
  have eq8973 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8857 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8857
    | (have j0 := eq8857 X1 (τ X0)
       grind)
    | exact resolve eq8857 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9028 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8857 y x
       grind)
    | exact superpose eq8857 eq16
    | (have j1 := eq8857 y x
       grind)
    | exact resolve eq16 eq8857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8857
  have eq9131 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8973 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq8973
    | (have j0 := eq8973 X0 X1
       grind)
    | exact resolve eq8973 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8973
  have eq9219 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq8738 X0 X1
       grind)
    | exact superpose eq8738 eq11
    | (have j1 := eq8738 X0 X1
       grind)
    | exact resolve eq11 eq8738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8738
  have eq9347 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9219 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq9219
    | (have j0 := eq9219 X0 X1
       grind)
    | exact resolve eq9219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9219
  have eq9443 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq9347 X0 X1
       grind)
    | exact superpose eq9347 eq11
    | (have j1 := eq9347 X0 X1
       grind)
    | exact resolve eq11 eq9347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347
  have eq9571 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9443 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9443
    | (have j0 := eq9443 X0 X1
       grind)
    | exact resolve eq9443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9443
  have eq9719 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9028
       have i₂ := eq9571 x y
       grind)
    | exact superpose eq9571 eq9028
    | (have j1 := eq9571 x y
       grind)
    | exact resolve eq9028 eq9571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9028
  have eq9720 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9571 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9571
  have eq9722 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (k y x) := by grind
  clear eq9719
  have eq9724 : x = (M.op x y) ∨ x = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq9722
       have r₂ := eq13 y x
       grind)
    | exact resolve eq9722 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9722
  have eq9742 : y = (k y x) ∨ x = (k y x) := by
    first
    | (have j1 := eq9720 y x
       grind)
    | (have r₁ := eq9724
       have r₂ := eq9720 y x
       grind)
    | exact resolve eq9724 eq9720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9720 eq9724
  have eq10747 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) ∨ (τ X1) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq9131 X0 (τ X1)
       grind)
    | exact superpose eq9131 eq17
    | (have j1 := eq9131 X0 (τ X1)
       grind)
    | exact resolve eq17 eq9131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10779 : ∀ X0 X1 : G, (τ X1) ≠ X0 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9131 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9131
  have eq10811 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) ∨ (τ X1) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10747 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10747
    | (have j0 := eq10747 X0 X1
       grind)
    | exact resolve eq10747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10747
  have eq10879 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (τ X1) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10811 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10811
    | (have j0 := eq10811 X0 X1
       grind)
    | exact resolve eq10811 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10811
  have eq10921 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10879 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq10879
    | (have j0 := eq10879 X0 X1
       grind)
    | exact resolve eq10879 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10879
  have eq10952 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10779 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10779
    | (have j0 := eq10779 X1 (σ X0)
       grind)
    | (have r₁ := eq10779 X0 (σ X0)
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq10779 (τ (σ (τ X1))) X1
       have r₂ := eq10 (τ X1)
       grind)
    | exact resolve eq10779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10779
  have eq10974 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10952 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10952
    | (have j0 := eq10952 X0 X1
       grind)
    | (have r₁ := eq10952 (σ (k X0 X1)) (k (σ X0) (σ X1))
       have r₂ := eq15 X0 X1
       grind)
    | (have r₁ := eq10952 (k (σ X0) (σ X1)) (σ (k X0 X1))
       have r₂ := eq15 X0 X1
       grind)
    | exact resolve eq10952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10952
  have eq10977 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10921 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10921
    | exact resolve eq10921 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10921
  have eq11163 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10977 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq10977
    | (have j0 := eq10977 X0 X1
       grind)
    | exact resolve eq10977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10977
  have eq11168 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11163 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11163
    | (have j0 := eq11163 X0 X1
       grind)
    | exact resolve eq11163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11163
  have eq11874 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq432
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq432
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq432 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11875 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq11874
  have eq12119 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11168 y x
       grind)
    | exact superpose eq11168 eq16
    | (have j1 := eq11168 y x
       grind)
    | exact resolve eq16 eq11168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11168
  have eq33774 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq749 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq34144 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33774 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq33774
    | (have j0 := eq33774 (τ X1) (τ X0)
       grind)
    | exact resolve eq33774 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33774
  have eq34247 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34144 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq34144
    | (have j0 := eq34144 X0 X1
       grind)
    | exact resolve eq34144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34144
  have eq34289 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34247 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34247
    | (have j0 := eq34247 X0 X1
       grind)
    | exact resolve eq34247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34247
  have eq34321 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34289 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34289
    | (have j0 := eq34289 X0 X1
       grind)
    | exact resolve eq34289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34289
  have eq34345 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34321 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq34321
    | (have j0 := eq34321 X0 X1
       grind)
    | exact resolve eq34321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34321
  have eq34357 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34345 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq34345
    | (have j0 := eq34345 X0 X1
       grind)
    | exact resolve eq34345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34345
  have eq34366 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34357 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq34357
    | (have j0 := eq34357 X0 X1
       grind)
    | exact resolve eq34357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34357
  have eq54394 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq11875
       grind)
    | exact superpose eq11875 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11875
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11875
       grind)
    | exact resolve eq13 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875
  have eq54429 : x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq54394
  have eq54433 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq10974 x y
       grind)
    | (have r₁ := eq54429
       have r₂ := eq10974 x y
       grind)
    | (have r₁ := eq54429
       have r₂ := eq10974 y x
       grind)
    | (have r₁ := eq54429
       have r₂ := eq10974 y (k y x)
       grind)
    | exact resolve eq54429 eq10974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10974 eq54429
  have eq74482 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7401 x y
       grind)
    | exact superpose eq7401 eq16
    | (have j1 := eq7401 x y
       grind)
    | exact resolve eq16 eq7401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7401
  have eq826716 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (σ X1))) ∨ (k (τ (τ (σ X0))) X1) = X1 ∨ (k (τ (τ (σ X0))) X1) = (τ (M.op (σ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (σ X1)
       have i₂ := eq8695 (σ X0) X1
       grind)
    | exact superpose eq8695 eq15
    | (have j1 := eq8695 (σ X0) X1
       grind)
    | exact resolve eq15 eq8695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8695
  have eq826953 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ X0) = (σ (k X0 (σ X1))) ∨ (k (τ (τ (σ X0))) X1) = (τ (M.op (σ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq826716 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq826716
    | (have j0 := eq826716 X0 X1
       grind)
    | exact resolve eq826716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826716
  have eq827120 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (k (τ X0) X1) = X1 ∨ (σ X0) = (σ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq826953 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq826953
    | (have j0 := eq826953 X0 X1
       grind)
    | exact resolve eq826953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826953
  have eq827878 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = X1 ∨ (σ X0) = (σ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq827120 X0 X1
       grind)
    | exact superpose eq827120 eq11
    | (have j1 := eq827120 X0 X1
       grind)
    | exact resolve eq11 eq827120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827120
  have eq828160 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = X1 ∨ (σ X0) = (σ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq827878 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq827878
    | (have j0 := eq827878 X0 X1
       grind)
    | exact resolve eq827878 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq827878
  have eq829307 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq828160 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq828160
    | (have j0 := eq828160 X1 (τ X0)
       grind)
    | exact resolve eq828160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828160
  have eq829831 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq829307 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq829307
    | (have j0 := eq829307 X0 X1
       grind)
    | exact resolve eq829307 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829307
  have eq830448 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq829831 X0 X1
       grind)
    | exact superpose eq829831 eq11
    | (have j1 := eq829831 X0 X1
       grind)
    | exact resolve eq11 eq829831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829831
  have eq830792 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq830448 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq830448
    | (have j0 := eq830448 X0 X1
       grind)
    | exact resolve eq830448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830448
  have eq831177 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq830792 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq830792
    | exact resolve eq830792 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq830792
  have eq832008 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq831177 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq831177
    | (have j0 := eq831177 X0 X1
       grind)
    | exact resolve eq831177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831177
  have eq832069 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq832008 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq832008
    | (have j0 := eq832008 X0 X1
       grind)
    | exact resolve eq832008 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832008
  have eq843209 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq832069 X1 X0
       grind)
    | exact superpose eq832069 eq11
    | (have j1 := eq832069 X1 X0
       grind)
    | exact resolve eq11 eq832069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832069
  have eq843565 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq843209 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq843209
    | (have j0 := eq843209 X0 X1
       grind)
    | exact resolve eq843209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843209
  have eq844210 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq843565 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq843565
    | exact resolve eq843565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844574 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = (M.op (τ X1) (τ (σ X0))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq843565 X1 (σ X0)
       grind)
    | exact superpose eq843565 eq28
    | (have j1 := eq843565 X1 (σ X0)
       grind)
    | exact resolve eq28 eq843565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843565
  have eq844990 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ (k (σ X0) X1)) = (M.op (τ X1) (τ (σ X0))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq844574 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq844574
    | (have j0 := eq844574 X0 X1
       grind)
    | exact resolve eq844574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844574
  have eq845177 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq844210 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq844210
    | (have j0 := eq844210 X0 X1
       grind)
    | exact resolve eq844210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844210
  have eq845379 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq844990 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq844990
    | (have j0 := eq844990 X0 X1
       grind)
    | exact resolve eq844990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844990
  have eq845518 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq845177 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq845177
    | (have j0 := eq845177 X0 X1
       grind)
    | exact resolve eq845177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845177
  have eq845645 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq845379 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq845379
    | (have j0 := eq845379 X0 X1
       grind)
    | exact resolve eq845379 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq845379
  have eq845691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq845518 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq845518
    | (have j0 := eq845518 X0 X1
       grind)
    | exact resolve eq845518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845518
  have eq851722 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq845645 X1 X0
       grind)
    | exact superpose eq845645 eq18
    | (have j1 := eq845645 X1 X0
       grind)
    | exact resolve eq18 eq845645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq845645
  have eq856672 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq845691 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845691
  have eq884327 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq851722 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq851722
    | (have j0 := eq851722 (σ X0) X1
       grind)
    | exact resolve eq851722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851722
  have eq884984 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq884327 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq884327
    | (have j0 := eq884327 X0 X1
       grind)
    | exact resolve eq884327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884327
  have eq885122 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq884984 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq884984
    | (have j0 := eq884984 X0 X1
       grind)
    | exact resolve eq884984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884984
  have eq888018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12119
       have i₂ := eq885122 x y
       grind)
    | exact superpose eq885122 eq12119
    | (have j1 := eq885122 x y
       grind)
    | (have r₁ := eq12119
       have r₂ := eq885122 x y
       grind)
    | exact resolve eq12119 eq885122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12119
  have eq888494 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq885122 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885122
  have eq888500 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq888018
  have eq888501 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq888500
  have eq888651 : y = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have j1 := eq888494 y x
       grind)
    | (have r₁ := eq888501
       have r₂ := eq888494 y x
       grind)
    | exact resolve eq888501 eq888494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888494 eq888501
  have eq888909 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq34366 y x
       have i₂ := eq888651
       grind)
    | exact superpose eq888651 eq34366
    | (have j0 := eq34366 y x
       grind)
    | (have r₁ := eq34366 y x
       have r₂ := eq888651
       grind)
    | exact resolve eq34366 eq888651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34366
  have eq888943 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq888909
  have eq888968 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq888943
       grind)
    | exact superpose eq888943 eq16
    | exact resolve eq16 eq888943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888943
  have eq889116 : y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq888968
       have r₂ := eq464 x
       grind)
    | exact resolve eq888968 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888968
  have eq889192 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq74482
       have i₂ := eq889116
       grind)
    | exact superpose eq889116 eq74482
    | exact resolve eq74482 eq889116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74482
  have eq889297 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq889192
  have eq889298 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq889297
  have eq890481 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq889298
       grind)
    | exact superpose eq889298 eq11
    | exact resolve eq11 eq889298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889298
  have eq890837 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq890481
       grind)
    | exact superpose eq890481 eq16
    | exact resolve eq16 eq890481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890481
  have eq891236 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq890837
       have i₂ := eq9742
       grind)
    | exact superpose eq9742 eq890837
    | exact resolve eq890837 eq9742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9742 eq890837
  have eq891285 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq891236
       have i₂ := eq889116
       grind)
    | exact superpose eq889116 eq891236
    | exact resolve eq891236 eq889116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889116 eq891236
  have eq891303 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq891285
  have eq891317 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq891303
       have i₂ := eq888651
       grind)
    | exact superpose eq888651 eq891303
    | exact resolve eq891303 eq888651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888651 eq891303
  have eq891349 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq891317
  have eq891406 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq891349
       grind)
    | exact superpose eq891349 eq16
    | exact resolve eq16 eq891349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891349
  have eq891570 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq891406
       have r₂ := eq464 x
       grind)
    | exact resolve eq891406 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891406
  have eq891630 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq891570
       grind)
    | exact superpose eq891570 eq10
    | exact resolve eq10 eq891570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891570
  have eq892237 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq891630
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq891630
    | exact resolve eq891630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891630
  have eq892250 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq892237
       grind)
    | exact superpose eq892237 eq16
    | exact resolve eq16 eq892237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892237
  have eq892414 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq892250
       have r₂ := eq464 x
       grind)
    | exact resolve eq892250 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892250
  have eq892532 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq892414
       grind)
    | exact superpose eq892414 eq10
    | exact resolve eq10 eq892414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893192 : x = (k y x) := by
    first
    | (have i₁ := eq892532
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq892532
    | exact resolve eq892532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892532
  have eq1106795 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq54433
       grind)
    | exact superpose eq54433 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq54433
       grind)
    | exact resolve eq13 eq54433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106885 : (σ y) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq54433
  have eq1106904 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq1106795
  have eq1106931 : (σ x) ≠ (σ y) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1106885
       have i₂ := eq892414
       grind)
    | exact superpose eq892414 eq1106885
    | exact resolve eq1106885 eq892414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106885
  have eq1107021 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1106904
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1106904
    | exact resolve eq1106904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106904
  have eq1107098 : x = y ∨ (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1106931
       have i₂ := eq893192
       grind)
    | exact superpose eq893192 eq1106931
    | exact resolve eq1106931 eq893192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106931
  have eq1107174 : (σ y) = (σ (k y x)) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq856672 y x
       grind)
    | (have r₁ := eq1107021
       have r₂ := eq856672 y (k y x)
       grind)
    | (have r₁ := eq1107021
       have r₂ := eq856672 (k y x) y
       grind)
    | (have r₁ := eq1107021
       have r₂ := eq856672 x y
       grind)
    | exact resolve eq1107021 eq856672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856672 eq1107021
  have eq1107228 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) ≠ (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1107098
       have i₂ := eq892414
       grind)
    | exact superpose eq892414 eq1107098
    | exact resolve eq1107098 eq892414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107098
  have eq1107300 : (σ x) = (σ y) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1107174
       have i₂ := eq892414
       grind)
    | exact superpose eq892414 eq1107174
    | exact resolve eq1107174 eq892414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107174
  have eq1107349 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq1107228
       have i₂ := eq893192
       grind)
    | exact superpose eq893192 eq1107228
    | exact resolve eq1107228 eq893192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107228
  have eq1107395 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1107300
       have i₂ := eq893192
       grind)
    | exact superpose eq893192 eq1107300
    | exact resolve eq1107300 eq893192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107300
  have eq1107439 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1107395
       have i₂ := eq892414
       grind)
    | exact superpose eq892414 eq1107395
    | exact resolve eq1107395 eq892414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107395
  have eq1107458 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1107439
       have i₂ := eq893192
       grind)
    | exact superpose eq893192 eq1107439
    | exact resolve eq1107439 eq893192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107439
  have eq1107473 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1107458
       have r₂ := eq1107349
       grind)
    | exact resolve eq1107458 eq1107349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107349 eq1107458
  have eq1107509 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq432
       have i₂ := eq1107473
       grind)
    | exact superpose eq1107473 eq432
    | exact resolve eq432 eq1107473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq1107473
  have eq1107693 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1107509
  have eq1107726 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1107693
       have i₂ := eq892414
       grind)
    | exact superpose eq892414 eq1107693
    | exact resolve eq1107693 eq892414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107693
  have eq1107727 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1107726
  have eq1107733 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1107727
       grind)
    | exact superpose eq1107727 eq16
    | exact resolve eq16 eq1107727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107727
  have eq1107993 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1107733
       have r₂ := eq464 x
       grind)
    | exact resolve eq1107733 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq1107733
  have eq1108148 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1107993
       grind)
    | exact superpose eq1107993 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1107993
       grind)
    | exact resolve eq13 eq1107993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108238 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1107993
  have eq1108257 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1108148
  have eq1108352 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1108257
       have r₂ := eq1108238
       grind)
    | exact resolve eq1108257 eq1108238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108257
  have eq1108436 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1108352
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1108352
    | exact resolve eq1108352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108352
  have eq1108492 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1108436
       have i₂ := eq892414
       grind)
    | exact superpose eq892414 eq1108436
    | exact resolve eq1108436 eq892414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892414 eq1108436
  have eq1108540 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1108492
       have r₂ := eq1108238
       grind)
    | exact resolve eq1108492 eq1108238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108238 eq1108492
  have eq1108623 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1108540
       grind)
    | exact superpose eq1108540 eq16
    | exact resolve eq16 eq1108540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108540
  have eq1109310 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1108623
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1108623
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1108623 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109318 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq1109310
  have eq1109325 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1109318
       have i₂ := eq893192
       grind)
    | exact superpose eq893192 eq1109318
    | exact resolve eq1109318 eq893192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109318
  have eq1109359 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1109325
       grind)
    | exact superpose eq1109325 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1109325
       grind)
    | exact resolve eq13 eq1109325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109449 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1109325
  have eq1109468 : x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1109359
  have eq1109504 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1109468
       have r₂ := eq1109449
       grind)
    | exact resolve eq1109468 eq1109449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109468
  have eq1109514 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1109504
       have i₂ := eq893192
       grind)
    | exact superpose eq893192 eq1109504
    | exact resolve eq1109504 eq893192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893192 eq1109504
  have eq1109515 : x = (M.op x y) := by
    first
    | (have r₁ := eq1109514
       have r₂ := eq1109449
       grind)
    | exact resolve eq1109514 eq1109449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109449 eq1109514
  have eq1109577 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1108623
       have i₂ := eq1109515
       grind)
    | exact superpose eq1109515 eq1108623
    | exact resolve eq1108623 eq1109515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108623 eq1109515
  have eq1109699 : False := by grind
  exact eq1109699

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq73
  have eq95 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq552 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X1) (σ X0)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq51
    | (have j1 := eq70 X1 X1
       grind)
    | exact resolve eq51 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq555 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq556 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq555 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq776 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x X0 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq3803 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq556 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq556
    | (have j0 := eq556 (τ X0)
       grind)
    | exact resolve eq556 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq556
  have eq3811 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3803 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3803
    | (have j0 := eq3803 X0
       grind)
    | exact resolve eq3803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3803
  have eq3817 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3811 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3811
    | (have j0 := eq3811 X0
       grind)
    | exact resolve eq3811 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811
  have eq5109 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq170 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq170
    | (have j0 := eq170 x
       grind)
    | exact resolve eq170 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq5137 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5109
  have eq5142 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5137
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5137
    | exact resolve eq5137 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5137
  have eq20724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq20724
    | exact resolve eq20724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20724
  have eq20736 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20725
       have r₂ := eq28
       grind)
    | exact resolve eq20725 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20725
  have eq20750 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  have eq20756 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20736 eq55
    | exact resolve eq55 eq20736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20736
  have eq20790 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq20756
    | exact resolve eq20756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20756
  have eq20796 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20790 eq780
    | exact resolve eq780 eq20790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20790
  have eq20858 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq53 eq20796
    | exact resolve eq20796 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20796
  have eq20860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq20858
    | exact resolve eq20858 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20858
  have eq20861 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20860
  have eq20889 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq20861
       grind)
    | exact superpose eq20861 eq75
    | exact resolve eq75 eq20861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq20937 : x ≠ y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20861
  have eq20942 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20889
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20889
    | exact resolve eq20889 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20889
  have eq25386 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20942
       have r₂ := eq20937
       grind)
    | exact resolve eq20942 eq20937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20937 eq20942
  have eq25387 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5142 eq25386
    | exact resolve eq25386 eq5142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142 eq25386
  have eq48327 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25387 eq55
    | exact resolve eq55 eq25387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25387
  have eq48395 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq48327
    | exact resolve eq48327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48327
  have eq48396 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48395
  have eq48407 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48396 eq780
    | exact resolve eq780 eq48396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48396
  have eq48526 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53 eq48407
    | exact resolve eq48407 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48407
  have eq48530 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq48526
    | exact resolve eq48526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48526
  have eq48531 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48530
  have eq48555 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48531
  have eq48942 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq552 x x
       have i₂ := eq48555
       grind)
    | exact superpose eq48555 eq552
    | (have j0 := eq552 x x
       grind)
    | exact resolve eq552 eq48555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq48555
  have eq48945 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48942
  have eq48962 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48945
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48945
    | exact resolve eq48945 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq48945
  have eq49940 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48962 eq780
    | exact resolve eq780 eq48962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq48962
  have eq50058 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53 eq49940
    | exact resolve eq49940 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq49940
  have eq50062 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq50058
    | exact resolve eq50058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq50058
  have eq50063 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq50062
  have eq50066 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq50063 eq28
    | exact resolve eq28 eq50063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq50063
  have eq762115 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20750 eq107
    | exact resolve eq107 eq20750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq20750
  have eq762162 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq762115
  have eq762172 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq762162
       have r₂ := eq50066
       grind)
    | exact resolve eq762162 eq50066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762162
  have eq765364 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq762172
  have eq766589 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq765364 eq69
    | exact resolve eq69 eq765364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq765364
  have eq766726 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq766589
    | exact resolve eq766589 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq766589
  have eq766729 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3817 x
       grind)
    | (have r₁ := eq766726
       have r₂ := eq3817 x
       grind)
    | exact resolve eq766726 eq3817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817 eq766726
  have eq766854 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq766729
       grind)
    | exact superpose eq766729 eq55
    | exact resolve eq55 eq766729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq766729
  have eq767337 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq766854
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq766854
    | exact resolve eq766854 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766854
  have eq767390 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq776 x
       have i₂ := eq767337
       grind)
    | exact superpose eq767337 eq776
    | exact resolve eq776 eq767337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq767337
  have eq768050 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq767390
    | exact resolve eq767390 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq767390
  have eq768079 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq768050
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq768050
    | exact resolve eq768050 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq768050
  have eq768080 : y = (M.op x y) := by grind
  clear eq768079
  have eq768084 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq768080 eq21
    | exact resolve eq21 eq768080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq768080
  have eq768738 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq768084
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq768084
    | exact resolve eq768084 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq768084
  have eq768739 : False := by grind
  exact eq768739

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq1499 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1538 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1499 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1539 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1538 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1681 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1539 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539
  have eq1684 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1681 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1681 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1681 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq1681 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq1681 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq1736 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq1684 X1 (τ X0)
       grind)
    | exact superpose eq1684 eq19
    | (have j1 := eq1684 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1739 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1684 (σ X1) (σ X0)
       grind)
    | exact superpose eq1684 eq15
    | (have j1 := eq1684 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1850 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1736 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1736
    | exact resolve eq1736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1911 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1850 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1850
    | (have j0 := eq1850 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq2531 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1739 x y
       grind)
    | exact superpose eq1739 eq16
    | (have j1 := eq1739 x y
       grind)
    | exact resolve eq16 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq2581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2531
       have i₂ := eq1911 x y
       grind)
    | exact superpose eq1911 eq2531
    | (have j1 := eq1911 (σ x) (σ y)
       grind)
    | (have r₁ := eq2531
       have r₂ := eq1911 x y
       grind)
    | (have r₁ := eq2531
       have r₂ := eq1911 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2531
       have r₂ := eq1911 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2531 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911 eq2531
  have eq2582 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2581
  have eq2732 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2582
       grind)
    | exact superpose eq2582 eq10
    | exact resolve eq10 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582
  have eq2782 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2732
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2732
    | exact resolve eq2732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq2783 : x = y := by grind
  clear eq2782
  have eq2785 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2783
       grind)
    | exact superpose eq2783 eq16
    | exact resolve eq16 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2786 : False := by grind
  exact eq2786

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation3263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
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
  clear eq22
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op x (M.op x y))) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 x)
       have i₂ := eq14 X0 X0 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq75 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
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
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq76
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq75
    | exact resolve eq75 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq75
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq44
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq44 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq130 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq133 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq130
    | exact resolve eq130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133
    | exact resolve eq133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq91
    | (have j0 := eq91 (σ x) (σ y)
       grind)
    | exact resolve eq91 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq134
  have eq202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq201
    | exact resolve eq201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq205 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq202
       have r₂ := eq27
       grind)
    | exact resolve eq202 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq207 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq205
    | exact resolve eq205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq207 eq52
    | exact resolve eq52 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq274
    | (have j0 := eq274 X0
       grind)
    | exact resolve eq274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq292 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq207 eq288
    | exact resolve eq288 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq305 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq338 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq305
    | (have j0 := eq305 (σ x)
       grind)
    | exact resolve eq305 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq357 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq338 eq77
    | exact resolve eq77 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq338
  have eq395 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq357
       grind)
    | exact superpose eq357 eq55
    | exact resolve eq55 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq466 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (τ (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq207 eq395
    | exact resolve eq395 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq484 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq466 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq488 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq484
    | exact resolve eq484 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq498 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq488 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq488
    | (have j0 := eq488 x
       grind)
    | exact resolve eq488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq536 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq357
       have i₂ := eq498
       grind)
    | exact superpose eq498 eq357
    | exact resolve eq357 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq498
  have eq543 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq536
  have eq548 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq207 eq543
    | exact resolve eq543 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq543
  have eq554 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by grind
  clear eq548
  have eq556 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq554
    | exact resolve eq554 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq554
  have eq557 : y = (M.op x y) := by grind
  clear eq556
  have eq559 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq557 eq20
    | exact resolve eq20 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq561 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq557 eq51
    | exact resolve eq51 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq570 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq561
    | (have j0 := eq561 X0
       grind)
    | exact resolve eq561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq572 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq559
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq559
    | exact resolve eq559 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq575 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq557 eq570
    | exact resolve eq570 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq579 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq572 eq26
    | exact resolve eq26 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq839 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq575 x
       grind)
    | exact superpose eq575 eq18
    | (have j1 := eq575 x
       grind)
    | exact resolve eq18 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq842 : y = (M.op x x) := by
    first
    | exact superpose eq557 eq839
    | exact resolve eq839 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq839
  have eq862 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq842
       grind)
    | exact superpose eq842 eq78
    | exact resolve eq78 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq842
  have eq878 : (σ y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq862
       have i₂ := eq575 sF2
       grind)
    | exact superpose eq575 eq862
    | exact resolve eq862 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq883 : (σ y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq878
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq878
    | exact resolve eq878 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq878
  have eq884 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq572 eq883
    | exact resolve eq883 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq883
  have eq901 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq884 eq14
    | exact resolve eq14 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq579 eq901
    | exact resolve eq901 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq913 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq902 X0
       have i₂ := eq575 X0
       grind)
    | (have i₁ := eq902 y
       have i₂ := eq575 y
       grind)
    | exact superpose eq575 eq902
    | exact resolve eq902 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq902 X0
       grind)
    | (have i₁ := eq52 (M.op (σ x) (σ y))
       have i₂ := eq902 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq902 eq52
    | exact resolve eq52 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq947 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq902 eq921
    | exact resolve eq921 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq921
  have eq951 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) y)) := by
    intro X0
    first
    | (have i₁ := eq947 X0
       have i₂ := eq575 sF2
       grind)
    | exact superpose eq575 eq947
    | exact resolve eq947 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq947
  have eq955 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq884 eq951
    | exact resolve eq951 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1089 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq913 eq955
    | exact resolve eq955 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq955
  have eq1316 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1089 eq579
    | exact resolve eq579 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq1089
  have eq1318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq884 eq1316
    | exact resolve eq1316 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq1316
  have eq1324 : False := by grind
  exact eq1324

/-- `Equation3263`: `x ◇ x = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation3263 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3263 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3263.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 x)
       have i₂ := eq14 X0 X0 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 (M.op y y) y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq77
    | exact resolve eq77 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq421 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq58
    | exact resolve eq58 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq17806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq17807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq17806
    | exact resolve eq17806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17806
  have eq17818 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq17807
       have r₂ := eq28
       grind)
    | exact resolve eq17807 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17807
  have eq17822 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17818 eq127
    | exact resolve eq127 eq17818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq17818
  have eq17875 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq17822
    | exact resolve eq17822 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17822
  have eq17876 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17875
  have eq17887 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq58 y X0
       have i₂ := eq17876
       grind)
    | exact superpose eq17876 eq58
    | exact resolve eq58 eq17876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq17894 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq421 y X0
       have i₂ := eq17876
       grind)
    | exact superpose eq17876 eq421
    | exact resolve eq421 eq17876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq17876
  have eq17926 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17894 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17894
    | (have j0 := eq17894 X0
       grind)
    | exact resolve eq17894 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17894
  have eq18169 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17887 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17887
    | (have j0 := eq17887 x
       grind)
    | exact resolve eq17887 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17887
  have eq18324 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq18169
       grind)
    | exact superpose eq18169 eq52
    | exact resolve eq52 eq18169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq18169
  have eq18372 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq18324
    | exact resolve eq18324 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18324
  have eq18766 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17926
    | (have j0 := eq17926 (σ x)
       grind)
    | exact resolve eq17926 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17926
  have eq19036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18766 eq18372
    | exact resolve eq18372 eq18766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18372 eq18766
  have eq19070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19036
  have eq19076 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19070
       have r₂ := eq28
       grind)
    | exact resolve eq19070 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19070
  have eq19079 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq19076 eq30
    | exact resolve eq30 eq19076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19076
  have eq19187 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq19079
    | exact resolve eq19079 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19079
  have eq19188 : x = y := by grind
  clear eq19187
  have eq19207 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19188
       grind)
    | exact superpose eq19188 eq19
    | exact resolve eq19 eq19188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19208 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq19188
       grind)
    | exact superpose eq19188 eq25
    | exact resolve eq25 eq19188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19188
  have eq19309 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19208
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19208
    | exact resolve eq19208 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19208
  have eq19325 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19309 eq27
    | exact resolve eq27 eq19309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19309
  have eq19532 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19325 eq70
    | exact resolve eq70 eq19325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq19325
  have eq19581 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19532
       have i₂ := eq19207
       grind)
    | exact superpose eq19207 eq19532
    | exact resolve eq19532 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19207 eq19532
  have eq19591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19581 eq15
    | exact resolve eq15 eq19581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19581
  have eq19645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19591
    | exact resolve eq19591 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19591
  have eq19656 : False := by grind
  exact eq19656
