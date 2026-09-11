import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyx_pxy_Equation3607 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op (M.op X1 X3) X0)
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq99 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq99 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq88 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq88 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq199 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq105 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq319 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X0) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X3) X0) (M.op X3 X1) X2
       have i₂ := eq19 X2 X3 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X2 X0 (M.op X1 X2)
       have i₂ := eq319 X1 X0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq319 eq19
    | exact resolve eq19 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq319
  have eq942 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq772 X2 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq772 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq772 eq9
    | exact resolve eq9 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1111 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1 X1
       have i₂ := eq942 X0 X0 X1
       grind)
    | exact superpose eq942 eq110
    | (have j0 := eq110 X0 X1 x
       grind)
    | exact resolve eq110 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq942
  have eq1180 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1111 X0 X1
       have j1 := eq199 X1 X0
       grind)
    | (have r₁ := eq1111 X1 X0
       have r₂ := eq199 X0 X1
       grind)
    | (have r₁ := eq1111 X0 X0
       have r₂ := eq199 X0 X0
       grind)
    | exact resolve eq1111 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq1111
  have eq1243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1180 (σ X1) (σ X0)
       grind)
    | exact superpose eq1180 eq15
    | exact resolve eq15 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1243 X0 X1
       have i₂ := eq1180 X1 X0
       grind)
    | exact superpose eq1180 eq1243
    | exact resolve eq1243 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq1243
  have eq1593 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1262 x y
       grind)
    | exact superpose eq1262 eq16
    | (have r₁ := eq16
       have r₂ := eq1262 x y
       grind)
    | exact resolve eq16 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1621 : False := by grind
  exact eq1621

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pxy_Equation3607 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X3) X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op (M.op X1 X3) X0)
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq518 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op (M.op X0 X1) X3) (M.op (M.op X3 X0) X2)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X3 X0 X2 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq55 X0 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq55
    | (have j1 := eq11 (M.op X2 X0) (M.op (M.op (M.op X0 X1) X3) (M.op (M.op X3 X0) X2))
       grind)
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq518 X0 X1 X2 x
       have i₂ := eq55 x X0 X2 X1
       grind)
    | exact superpose eq55 eq518
    | (have j0 := eq518 X0 X1 X2 x
       grind)
    | exact resolve eq518 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq518
  have eq1007 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq9430 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1007 X0 X1
       have j1 := eq552 (M.op X0 X1) (k X0 X1) x
       grind)
    | (have r₁ := eq1007 X0 X1
       have r₂ := eq552 X0 X1 X0
       grind)
    | (have r₁ := eq1007 X1 X0
       have r₂ := eq552 X0 X1 X1
       grind)
    | (have r₁ := eq1007 X0 X1
       have r₂ := eq552 (M.op X0 X1) (M.op X0 X0) x
       grind)
    | exact resolve eq1007 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq1007
  have eq9551 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq9430 x y
       grind)
    | exact superpose eq9430 eq49
    | (have j1 := eq9430 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq9430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq9707 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq9551
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9551
    | exact resolve eq9551 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9551
  have eq9717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq9707
    | exact resolve eq9707 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9707
  have eq9730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9717 eq9430
    | (have j0 := eq9430 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq9430 eq9717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9430 eq9717
  have eq9734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq9730
    | exact resolve eq9730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9730
  have eq9743 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9734
       have r₂ := eq28
       grind)
    | exact resolve eq9734 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9734
  have eq9747 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq9743 eq30
    | exact resolve eq30 eq9743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9743
  have eq9845 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq9747
    | exact resolve eq9747 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9747
  have eq9846 : x = y := by grind
  clear eq9845
  have eq9859 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq9846
       grind)
    | exact superpose eq9846 eq19
    | exact resolve eq19 eq9846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq9860 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq9846
       grind)
    | exact superpose eq9846 eq25
    | exact resolve eq25 eq9846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq9846
  have eq9970 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9860
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9860
    | exact resolve eq9860 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq9860
  have eq9985 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9970 eq27
    | exact resolve eq27 eq9970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9970
  have eq10179 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq9985 eq68
    | exact resolve eq68 eq9985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq9985
  have eq10231 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10179
       have i₂ := eq9859
       grind)
    | exact superpose eq9859 eq10179
    | exact resolve eq10179 eq9859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9859 eq10179
  have eq10244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10231 eq15
    | exact resolve eq15 eq10231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10231
  have eq10286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10244
    | exact resolve eq10244 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq10244
  have eq10295 : False := by grind
  exact eq10295

/-- `Equation3617`: `x ◇ y = z ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_x_pxy_Equation3617 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3617 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3617.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
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
  have eq50 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X1) X3 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X3 X2) X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op X3 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X0) X1) ∨ (M.op (M.op (M.op X2 X0) X1) X2) = (k (M.op (M.op X2 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X0) X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X0) X1) X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 X0 (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq44
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq44 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq171 : (σ (k (k y x) y)) = (k (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq40 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq40
    | exact resolve eq40 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq72
  have eq199 : ∀ X0 X1 : G, (M.op y (M.op (M.op (M.op x y) X0) X1)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op sF0 X0) X1)
       have i₂ := eq14 X0 X1 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op sF4 X0) X1)
       have i₂ := eq14 X0 X1 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X0 X1)
       have i₂ := eq52 X1 X2 X0 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op (M.op X2 X0) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq52 X2 X0 X3 X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq114 eq90
    | (have j0 := eq90 x (σ y)
       grind)
    | exact resolve eq90 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq562
    | exact resolve eq562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq566 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq563
       have r₂ := eq27
       grind)
    | exact resolve eq563 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq569 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq566 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq566
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq566
       grind)
    | exact resolve eq13 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq573 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq569
  have eq578 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op x (M.op X0 (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq559 y X1 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq559
    | (have j0 := eq559 y X1 x X0
       grind)
    | exact resolve eq559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ x) (M.op X0 (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq559
    | (have j0 := eq559 (σ y) X1 (σ x) X0
       grind)
    | exact resolve eq559 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op (M.op (M.op X4 X3) X0) X1))) = (M.op X4 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq559 X3 (M.op (M.op (M.op X4 X3) X0) X1) X4 X2
       have i₂ := eq14 X0 X1 (M.op X4 X3)
       grind)
    | exact superpose eq14 eq559
    | exact resolve eq559 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X1 X0) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq559 X2 X3 X1 (M.op X1 X0)
       have i₂ := eq14 X0 (M.op (M.op X1 X2) X3) X1
       grind)
    | exact superpose eq14 eq559
    | exact resolve eq559 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq559
    | exact resolve eq559 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X3 (M.op X4 (M.op (M.op X3 X0) X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq584 X0 X1 X2 X3 X4
       have i₂ := eq52 X3 X0 X4 X1
       grind)
    | exact superpose eq52 eq584
    | exact resolve eq584 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq615 : ∀ X0 X1 X2 X4 : G, (M.op X4 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq611 X0 X1 X2 x X4
       have i₂ := eq559 X0 X1 x X4
       grind)
    | exact superpose eq559 eq611
    | exact resolve eq611 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq611
  have eq619 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq573 eq84
    | exact resolve eq84 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq573
  have eq623 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq619
    | exact resolve eq619 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq619
  have eq626 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90 y y
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq627 : y = (M.op y y) := by grind
  clear eq626
  have eq632 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq627
       grind)
    | exact superpose eq627 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq627
       grind)
    | exact resolve eq13 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq627
       grind)
    | exact superpose eq627 eq14
    | exact resolve eq14 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : y = (k y y) := by grind
  clear eq632
  have eq676 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq681 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq676
    | (have j0 := eq676 X0 X1
       grind)
    | exact resolve eq676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq697 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq636
       grind)
    | exact superpose eq636 eq73
    | exact resolve eq73 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq636
  have eq701 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq697
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq697
    | exact resolve eq697 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq704 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq701 eq90
    | (have j0 := eq90 x (σ y)
       grind)
    | exact resolve eq90 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq705 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq704
  have eq711 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq705 eq14
    | exact resolve eq14 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq633 (M.op (M.op y X0) X1)
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq633
    | exact resolve eq633 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq732 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X0) X1) ∨ (k (M.op (M.op X2 X0) X1) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq52 X0 X1 X2 X2
       grind)
    | exact superpose eq52 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq65
  have eq765 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq718 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq718
    | (have j0 := eq718 x y
       grind)
    | exact resolve eq718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : (M.op (σ x) (σ y)) = (M.op y (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq718
    | (have j0 := eq718 (σ x) (σ y)
       grind)
    | exact resolve eq718 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : (σ y) = (M.op y (σ y)) := by
    first
    | exact superpose eq705 eq718
    | exact resolve eq718 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (k (M.op y X0) y) = (M.op y (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq732 y x y
       have i₂ := eq627
       grind)
    | exact superpose eq627 eq732
    | exact resolve eq732 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op (σ y) X0) ∨ (M.op (σ y) (M.op (M.op (σ y) X0) (σ y))) = (k (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq705 eq732
    | exact resolve eq732 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq814 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ y) X0) (σ y))) = (k (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq806 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq818 : ∀ X0 : G, (k (M.op y X0) y) = (M.op y (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have j0 := eq800 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq822 : ∀ X0 : G, (k (M.op (σ y) X0) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq814 X0
       have i₂ := eq14 X0 sF3 sF3
       grind)
    | exact superpose eq14 eq814
    | exact resolve eq814 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq827 : ∀ X0 : G, (k (M.op y X0) y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq818 X0
       have i₂ := eq14 X0 y y
       grind)
    | exact superpose eq14 eq818
    | exact resolve eq818 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq921 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq718 (M.op sF0 X0) X1
       grind)
    | exact superpose eq718 eq199
    | exact resolve eq199 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq929 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op x (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq921 eq14
    | exact resolve eq14 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 (M.op (M.op sF3 X0) X1)
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq711
    | exact resolve eq711 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1039 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq770 eq963
    | (have j0 := eq963 (σ x) (σ y)
       grind)
    | exact resolve eq963 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1077 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq963 eq202
    | exact resolve eq202 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1112 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq1077 eq14
    | exact resolve eq14 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1161 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq578 eq50
    | exact resolve eq50 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1161 x
       have i₂ := eq718 sF0 x
       grind)
    | exact superpose eq718 eq1161
    | exact resolve eq1161 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1249 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq580 eq51
    | exact resolve eq51 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1264 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq963 eq1249
    | exact resolve eq1249 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1478 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq963 eq591
    | exact resolve eq591 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq963
  have eq1561 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq929 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq929
    | (have j0 := eq929 x y
       grind)
    | exact resolve eq929 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1566 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq929 y y
       have i₂ := eq627
       grind)
    | exact superpose eq627 eq929
    | exact resolve eq929 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq1574 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq929
    | (have j0 := eq929 (σ x) (σ y)
       grind)
    | exact resolve eq929 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1614 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1566
    | exact resolve eq1566 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1621 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1614 eq578
    | exact resolve eq578 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1641 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq765 eq1621
    | exact resolve eq1621 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq1621
  have eq1786 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq929 X0 y
       have i₂ := eq1641 X0
       grind)
    | (have i₁ := eq929 x y
       have i₂ := eq1641 x
       grind)
    | exact superpose eq1641 eq929
    | exact resolve eq929 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq1641
  have eq1914 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq1112
    | (have j0 := eq1112 (σ x) (σ y)
       grind)
    | exact resolve eq1112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1923 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq705 eq1112
    | exact resolve eq1112 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq1951 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1923
    | exact resolve eq1923 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq1956 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1951 eq580
    | exact resolve eq580 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq1973 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1039 eq1956
    | exact resolve eq1956 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq1956
  have eq2248 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1973 eq1112
    | exact resolve eq1112 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq1973
  have eq5452 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1914 eq588
    | exact resolve eq588 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914
  have eq5547 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq5452 X0 X1
       have i₂ := eq588 sF4 X1 sF2 sF4
       grind)
    | exact superpose eq588 eq5452
    | exact resolve eq5452 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5452
  have eq5675 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X1 (σ x)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2248 eq5547
    | exact resolve eq5547 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5547
  have eq5986 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1561 eq615
    | (have j0 := eq615 x y X0 X1
       grind)
    | exact resolve eq615 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq5988 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1574 eq615
    | (have j0 := eq615 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq615 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq6155 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op x y) (M.op X1 X2))) X3) = (M.op x (M.op (M.op X0 (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq921 (M.op X2 (M.op X0 X1)) X1
       have i₂ := eq615 X0 X1 X2 sF0
       grind)
    | (have i₁ := eq921 (M.op x (M.op X0 X1)) X1
       have i₂ := eq615 X0 X1 sF0 x
       grind)
    | exact superpose eq615 eq921
    | exact resolve eq921 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq921
  have eq6583 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x y)) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) (M.op X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5986 eq457
    | exact resolve eq457 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986
  have eq6682 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6583 X0 X1 X1
       have i₂ := eq588 X0 X1 (M.op X0 X1) (M.op X1 sF0)
       grind)
    | exact superpose eq588 eq6583
    | exact resolve eq6583 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6583
  have eq6764 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6682 X0 X1 X2
       have i₂ := eq588 (M.op X0 X1) X2 X2 sF0
       grind)
    | exact superpose eq588 eq6682
    | exact resolve eq6682 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6682
  have eq6797 : ∀ X1 X2 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op (M.op X2 X2) (M.op x y))) := by
    intro X1 X2
    first
    | (have i₁ := eq6764 X2 x X2
       have i₂ := eq14 x (M.op (M.op X2 X2) sF0) X2
       grind)
    | exact superpose eq14 eq6764
    | exact resolve eq6764 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6764
  have eq6939 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) (M.op X2 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5988 eq457
    | exact resolve eq457 eq5988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq5988
  have eq7038 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6939 X0 X1 X1
       have i₂ := eq588 X0 X1 (M.op X0 X1) (M.op X1 sF4)
       grind)
    | exact superpose eq588 eq6939
    | exact resolve eq6939 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6939
  have eq7119 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X2 X2) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7038 X0 X1 X2
       have i₂ := eq588 (M.op X0 X1) X2 X2 sF4
       grind)
    | exact superpose eq588 eq7038
    | exact resolve eq7038 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq7038
  have eq7149 : ∀ X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op X2 X2) (M.op (σ x) (σ y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq7119 X2 x X2
       have i₂ := eq14 x (M.op (M.op X2 X2) sF4) X2
       grind)
    | exact superpose eq14 eq7119
    | exact resolve eq7119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7119
  have eq8542 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq6797 eq1174
    | exact resolve eq1174 eq6797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6797
  have eq8581 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x y))) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq1786 eq8542
    | exact resolve eq8542 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786 eq8542
  have eq8666 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq1174 eq8581
    | exact resolve eq8581 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq8581
  have eq8700 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq1614 eq8666
    | exact resolve eq8666 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8666
  have eq13246 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq7149 eq1264
    | exact resolve eq1264 eq7149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7149
  have eq13262 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq2248 eq13246
    | exact resolve eq13246 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13246
  have eq13373 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1264 eq13262
    | exact resolve eq13262 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq13262
  have eq13438 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1951 eq13373
    | exact resolve eq13373 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq13373
  have eq72647 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op x y)) X1)) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6155 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6155
    | (have j0 := eq6155 X0 x y X1
       grind)
    | exact resolve eq6155 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6155
  have eq73434 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1614 eq72647
    | exact resolve eq72647 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614 eq72647
  have eq131471 : ∀ X0 : G, (M.op x (M.op (M.op X0 (M.op x y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0
    first
    | exact superpose eq5675 eq50
    | exact resolve eq50 eq5675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq5675
  have eq131587 : ∀ X0 : G, (M.op x (M.op (M.op X0 (M.op x y)) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq131471 X0
       have i₂ := eq718 (M.op X0 sF2) sF3
       grind)
    | exact superpose eq718 eq131471
    | exact resolve eq131471 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq131471
  have eq131886 : ∀ X0 : G, (M.op (M.op X0 y) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq73434 eq131587
    | exact resolve eq131587 eq73434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73434 eq131587
  have eq910986 : (k (k (σ y) (σ x)) (σ y)) = (σ (k (M.op y x) y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq171
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq171
    | (have j1 := eq90 x x
       grind)
    | exact resolve eq171 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq911069 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq910986
       have i₂ := eq827 x
       grind)
    | exact superpose eq827 eq910986
    | exact resolve eq910986 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq910986
  have eq911078 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq911069
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq911069
    | exact resolve eq911069 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911069
  have eq911087 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq911078
    | exact resolve eq911078 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911078
  have eq911093 : (σ (M.op x y)) = (k (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq911087
       have i₂ := eq90 sF3 sF2
       grind)
    | exact superpose eq90 eq911087
    | (have j1 := eq90 x x
       grind)
    | exact resolve eq911087 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq911112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq822 eq911093
    | exact resolve eq911093 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911093
  have eq911115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq911112
    | exact resolve eq911112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911112
  have eq911116 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq911115
       have r₂ := eq27
       grind)
    | exact resolve eq911115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911115
  have eq911141 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq911116 eq131886
    | exact resolve eq131886 eq911116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131886 eq911116
  have eq911489 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1478 eq911141
    | exact resolve eq911141 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq911141
  have eq911564 : (M.op (σ x) (σ y)) = (M.op y (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2248 eq911489
    | exact resolve eq911489 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248 eq911489
  have eq911610 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq772 eq911564
    | exact resolve eq911564 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq911564
  have eq911631 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq911610
    | exact resolve eq911610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911610
  have eq911700 : x ≠ x ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq911631
       grind)
    | exact superpose eq911631 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq911631
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq911631
       grind)
    | exact resolve eq13 eq911631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911631
  have eq911890 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq911700
  have eq914416 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq681 x x
       have i₂ := eq911890
       grind)
    | exact superpose eq911890 eq681
    | (have j0 := eq681 x x
       grind)
    | exact resolve eq681 eq911890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq911890
  have eq914423 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq914416
  have eq914424 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq914423
  have eq914435 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq914424
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq914424
    | exact resolve eq914424 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq914424
  have eq919257 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq914435 eq13438
    | exact resolve eq13438 eq914435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13438 eq914435
  have eq919593 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq919257
    | exact resolve eq919257 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919257
  have eq919594 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq919593
  have eq919759 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq919594 eq27
    | exact resolve eq27 eq919594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919761 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq919594 eq64
    | (have r₁ := eq64
       have r₂ := eq919594
       grind)
    | exact resolve eq64 eq919594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq919594
  have eq919929 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
  clear eq919761
  have eq922450 : (σ (M.op x y)) = (k (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq919929 eq911087
    | exact resolve eq911087 eq919929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911087 eq919929
  have eq922470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq822 eq922450
    | exact resolve eq922450 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq922450
  have eq922474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq922470
    | exact resolve eq922470 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq922470
  have eq922477 : x = (M.op x x) := by
    first
    | (have r₁ := eq922474
       have r₂ := eq27
       grind)
    | exact resolve eq922474 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq922474
  have eq922510 : y = (M.op x y) := by
    first
    | (have i₁ := eq8700 x
       have i₂ := eq922477
       grind)
    | exact superpose eq922477 eq8700
    | exact resolve eq8700 eq922477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8700 eq922477
  have eq922889 : y = (M.op x y) := by
    first
    | (have i₁ := eq922510
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq922510
    | exact resolve eq922510 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq922510
  have eq923198 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq922889 eq20
    | exact resolve eq20 eq922889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq922889
  have eq923600 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq923198
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq923198
    | exact resolve eq923198 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq923198
  have eq923690 : False := by grind
  exact eq923690

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq217 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq224 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq204 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq204 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq226 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq217 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq217 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq217 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq237 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq224
    | (have j0 := eq224 X0 X1
       grind)
    | exact resolve eq224 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq238 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq237 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq239 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq240 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq245 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq240 X0 X1
       have j1 := eq238 X0 X1
       grind)
    | (have r₁ := eq240 X0 X1
       have r₂ := eq238 X0 X1
       grind)
    | exact resolve eq240 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq240
  have eq246 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq245
    | exact resolve eq245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq245 x y
       grind)
    | exact superpose eq245 eq16
    | exact resolve eq16 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq338 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq246 X0 (τ X1)
       grind)
    | exact superpose eq246 eq17
    | exact resolve eq17 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq246
  have eq361 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq338
    | exact resolve eq338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq372 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq361
    | exact resolve eq361 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq396 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq257
       have i₂ := eq372 x y
       grind)
    | exact superpose eq372 eq257
    | exact resolve eq257 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq372
  have eq397 : False := by grind
  exact eq397

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pxx_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
  have eq270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq270 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq270 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq286 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq272 (σ X0)
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq272 (τ X0)
       grind)
    | exact superpose eq272 eq17
    | exact resolve eq17 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq298 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq293
    | exact resolve eq293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq305 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq286
    | exact resolve eq286 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq318 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq298
    | exact resolve eq298 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq298
  have eq342 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq10
    | exact resolve eq10 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq358 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq358 (σ X1) (σ X0)
       grind)
    | exact superpose eq358 eq15
    | (have j1 := eq358 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq358 (τ X1) (τ X0)
       grind)
    | exact superpose eq358 eq31
    | (have j1 := eq358 (τ X1) (τ X0)
       grind)
    | exact resolve eq31 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq405 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 X1
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq396
    | (have j0 := eq396 X0 X1
       grind)
    | exact resolve eq396 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq396
  have eq406 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq389
    | (have j0 := eq389 X0 X1
       grind)
    | exact resolve eq389 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq618 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq358 X1 X0
       grind)
    | exact superpose eq358 eq406
    | (have j0 := eq406 X0 X1
       have j1 := eq358 X1 X0
       grind)
    | exact resolve eq406 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq3345 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq3376 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X1) (σ X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3345 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3345
    | (have j0 := eq3345 (σ X1) (σ X0)
       grind)
    | exact resolve eq3345 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3441 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X1 X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3376 X0 X1
       have i₂ := eq305 X1
       grind)
    | exact superpose eq305 eq3376
    | (have j0 := eq3376 X0 X1
       grind)
    | exact resolve eq3376 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3469 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (σ (k X0 X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3441 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq3441
    | (have j0 := eq3441 X0 X1
       grind)
    | exact resolve eq3441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441
  have eq3490 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3469 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3469
    | (have j0 := eq3469 X0 X1
       grind)
    | exact resolve eq3469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469
  have eq3510 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3490 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3490
    | (have j0 := eq3490 X0 X1
       grind)
    | exact resolve eq3490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490
  have eq3525 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (M.op (σ X1) (σ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3510 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3510
    | (have j0 := eq3510 X0 X1
       grind)
    | exact resolve eq3510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq3539 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X1 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3525 X0 X1
       have i₂ := eq305 X1
       grind)
    | exact superpose eq305 eq3525
    | (have j0 := eq3525 X0 X1
       grind)
    | exact resolve eq3525 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525
  have eq3548 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3539 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq3539
    | (have j0 := eq3539 X0 X1
       grind)
    | exact resolve eq3539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539
  have eq3560 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3548 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3548
    | (have j0 := eq3548 (σ X0) (σ X1)
       grind)
    | exact resolve eq3548 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548
  have eq3586 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3560 X0 X1
       have i₂ := eq305 X1
       grind)
    | exact superpose eq305 eq3560
    | (have j0 := eq3560 X0 X1
       grind)
    | exact resolve eq3560 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3560
  have eq3594 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3586 X0 X1
       have i₂ := eq305 X1
       grind)
    | exact superpose eq305 eq3586
    | (have j0 := eq3586 X0 X1
       grind)
    | exact resolve eq3586 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq45096 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq10
    | (have j1 := eq618 X0 X1
       grind)
    | exact resolve eq10 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45237 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq618 x y
       grind)
    | exact superpose eq618 eq16
    | (have j1 := eq618 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq618 x y
       grind)
    | exact resolve eq16 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45252 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq9
    | (have j1 := eq618 X0 X1
       grind)
    | exact resolve eq9 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq45273 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45252 X0 X1
       have i₂ := eq305 X1
       grind)
    | exact superpose eq305 eq45252
    | (have j0 := eq45252 X0 X1
       grind)
    | exact resolve eq45252 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45252
  have eq45285 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq45237
       have r₂ := eq16
       grind)
    | exact resolve eq45237 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45237
  have eq45421 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45273 X0 X1
       have i₂ := eq305 (M.op X0 X0)
       grind)
    | exact superpose eq305 eq45273
    | (have j0 := eq45273 X0 X1
       grind)
    | exact resolve eq45273 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45273
  have eq45506 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45421 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq45421
    | (have j0 := eq45421 X0 X1
       grind)
    | exact resolve eq45421 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45421
  have eq61022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45506 x y
       grind)
    | exact superpose eq45506 eq16
    | (have j1 := eq45506 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq45506 x y
       grind)
    | exact resolve eq16 eq45506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45506
  have eq61058 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq61022
  have eq61313 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq61058
       grind)
    | exact superpose eq61058 eq10
    | exact resolve eq10 eq61058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61058
  have eq61614 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq61313
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq61313
    | exact resolve eq61313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61313
  have eq61690 : (M.op y y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq61614
       grind)
    | exact superpose eq61614 eq9
    | exact resolve eq9 eq61614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61614
  have eq61702 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq61690
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq61690
    | exact resolve eq61690 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61690
  have eq61703 : (M.op x x) = (M.op y y) := by grind
  clear eq61702
  have eq97477 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45096 x y
       grind)
    | exact superpose eq45096 eq16
    | (have j1 := eq45096 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq45096 x y
       grind)
    | exact resolve eq16 eq45096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45096
  have eq97501 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq97477
  have eq97738 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq97501
       grind)
    | exact superpose eq97501 eq11
    | exact resolve eq11 eq97501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97501
  have eq98213 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq342 x (σ y)
       have i₂ := eq97738
       grind)
    | exact superpose eq97738 eq342
    | (have j0 := eq342 x (σ y)
       grind)
    | (have r₁ := eq342 x (σ y)
       have r₂ := eq97738
       grind)
    | exact resolve eq342 eq97738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq98231 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq98213
  have eq98250 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98231
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq98231
    | exact resolve eq98231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98231
  have eq98268 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98250
       have i₂ := eq305 y
       grind)
    | exact superpose eq305 eq98250
    | exact resolve eq98250 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq98250
  have eq98280 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98268
       have i₂ := eq61703
       grind)
    | exact superpose eq61703 eq98268
    | exact resolve eq98268 eq61703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98268
  have eq98290 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq358 eq98280
    | (have j1 := eq358 y x
       grind)
    | exact resolve eq98280 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98280
  have eq98294 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq98290
       have r₂ := eq45285
       grind)
    | exact resolve eq98290 eq45285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98290
  have eq98324 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq98294
       grind)
    | exact superpose eq98294 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq98294
       grind)
    | exact resolve eq12 eq98294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98294
  have eq98334 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq98324
  have eq98344 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98334
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq98334
    | exact resolve eq98334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98334
  have eq98370 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq97738 eq98344
    | exact resolve eq98344 eq97738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97738 eq98344
  have eq98390 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq358 eq98370
    | (have j1 := eq358 y x
       grind)
    | exact resolve eq98370 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq98370
  have eq98401 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq98390
       have r₂ := eq45285
       grind)
    | exact resolve eq98390 eq45285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45285 eq98390
  have eq98413 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98401
       grind)
    | exact superpose eq98401 eq16
    | exact resolve eq16 eq98401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98422 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq98401
       grind)
    | exact superpose eq98401 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq98401
       grind)
    | exact resolve eq13 eq98401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98431 : y = (M.op y x) ∨ (M.op y y) = (k y x) := by grind
  clear eq98422
  have eq98440 : (M.op x x) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98431
       have i₂ := eq61703
       grind)
    | exact superpose eq61703 eq98431
    | exact resolve eq98431 eq61703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61703 eq98431
  have eq98462 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3594 y x
       have i₂ := eq98440
       grind)
    | exact superpose eq98440 eq3594
    | (have j0 := eq3594 y x
       grind)
    | exact resolve eq3594 eq98440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98440
  have eq98479 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by grind
  clear eq98462
  have eq98497 : y = (M.op y x) := by
    first
    | (have r₁ := eq98479
       have r₂ := eq98413
       grind)
    | exact resolve eq98479 eq98413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98479
  have eq98505 : y ≠ y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq98497
       grind)
    | exact superpose eq98497 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq98497
       grind)
    | exact resolve eq12 eq98497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98497
  have eq98515 : (M.op x y) = (k y x) := by grind
  clear eq98505
  have eq98516 : (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq98515
       have i₂ := eq98401
       grind)
    | exact superpose eq98401 eq98515
    | exact resolve eq98515 eq98401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98401 eq98515
  have eq98528 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3594 y x
       have i₂ := eq98516
       grind)
    | exact superpose eq98516 eq3594
    | (have j0 := eq3594 y x
       grind)
    | exact resolve eq3594 eq98516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594 eq98516
  have eq98545 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq98528
  have eq98563 : False := by grind
  exact eq98563

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_x_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq395 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq400 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq402 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq400 X0 (k X0 X0)
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq400 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq400 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq400 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq405 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq397
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq397 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq407 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq401 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq401 (M.op X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq401 (M.op X1 X0) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq401 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq401 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq408 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq405
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq405
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq409 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq407 X0 X1
       have j1 := eq402 X1 X0
       grind)
    | (have r₁ := eq407 X1 X0
       have r₂ := eq402 X0 X1
       grind)
    | (have r₁ := eq407 (M.op X0 X0) X1
       have r₂ := eq402 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq407 (M.op X0 X0) X1
       have r₂ := eq402 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq407 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq407
  have eq468 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq409 X1 (τ X0)
       grind)
    | exact superpose eq409 eq18
    | (have j1 := eq409 X1 (τ X0)
       grind)
    | exact resolve eq18 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq485 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq408
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq408
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq603
  have eq605 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq604
       have r₂ := eq12 y x
       grind)
    | exact resolve eq604 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq638 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq468 X1 (τ X0)
       grind)
    | exact superpose eq468 eq17
    | (have j1 := eq468 X1 (τ X0)
       grind)
    | exact resolve eq17 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq468
  have eq643 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq638 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq638
    | (have j0 := eq638 X0 X1
       grind)
    | exact resolve eq638 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq658 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq643
    | (have j0 := eq643 X0 X1
       grind)
    | exact resolve eq643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq663 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq727 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq409 X0 X1
       grind)
    | exact superpose eq409 eq663
    | (have j0 := eq663 X1 X0
       have j1 := eq409 X1 X0
       grind)
    | exact resolve eq663 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq663
  have eq792 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq727 X0 X1
       have j1 := eq485 X1 X0
       grind)
    | (have r₁ := eq727 X1 X0
       have r₂ := eq485 X0 X1
       grind)
    | exact resolve eq727 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq727
  have eq822 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq792 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq792
    | (have j0 := eq792 (σ X0) X1
       grind)
    | exact resolve eq792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1318 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq822 X1 (σ X0)
       grind)
    | exact superpose eq822 eq28
    | (have j1 := eq822 X1 (σ X0)
       grind)
    | exact resolve eq28 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq822
  have eq1330 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1318 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1318
    | (have j0 := eq1318 X0 X1
       grind)
    | exact resolve eq1318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1346 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1330 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1330
    | (have j0 := eq1330 X0 X1
       grind)
    | exact resolve eq1330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1357 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1346
    | (have j0 := eq1346 X0 X1
       grind)
    | exact resolve eq1346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1381 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1357 y x
       grind)
    | exact superpose eq1357 eq16
    | (have j1 := eq1357 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1357 y x
       grind)
    | exact resolve eq16 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1402 : y = (k y x) := by grind
  clear eq1381
  have eq1791 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq605
       have i₂ := eq1402
       grind)
    | exact superpose eq1402 eq605
    | exact resolve eq605 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq1798 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq408
       have i₂ := eq1791
       grind)
    | exact superpose eq1791 eq408
    | exact resolve eq408 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq1791
  have eq1807 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1798
  have eq1808 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1807
       have i₂ := eq1402
       grind)
    | exact superpose eq1402 eq1807
    | exact resolve eq1807 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq1809 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1808
  have eq1812 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq16
    | exact resolve eq16 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1839 : (σ y) ≠ (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1812
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1812
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1812 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1840 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1839
  have eq1842 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1840
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1840 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1843 : y = (M.op x y) := by
    first
    | (have i₁ := eq1842
       have i₂ := eq1402
       grind)
    | exact superpose eq1402 eq1842
    | exact resolve eq1842 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402 eq1842
  have eq1844 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1812
       have i₂ := eq1843
       grind)
    | exact superpose eq1843 eq1812
    | exact resolve eq1812 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq1843
  have eq1855 : False := by grind
  exact eq1855

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq70
  have eq97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | (have i₁ := eq81 X0
       have i₂ := eq14 (σ X0) (σ X0)
       grind)
    | exact superpose eq14 eq81
    | (have j1 := eq14 (σ (M.op X0 X0)) (M.op (σ X0) X1)
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq371 X0 X1
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq371 X0 X1
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq371 (M.op X0 X0) (M.op (σ X0) X1)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq371 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq371
  have eq386 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq376
    | exact resolve eq376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq376 X0 (σ X1)
       grind)
    | exact superpose eq376 eq15
    | (have j1 := eq376 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq426 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq386 (τ X0) X1
       grind)
    | exact superpose eq386 eq19
    | (have j1 := eq386 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq386
  have eq513 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq426 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq426
    | exact resolve eq426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq552 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq513
    | (have j0 := eq513 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq692 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq397 x y
       grind)
    | exact superpose eq397 eq16
    | (have j1 := eq397 x y
       grind)
    | exact resolve eq16 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq692
       have i₂ := eq552 x y
       grind)
    | exact superpose eq552 eq692
    | (have j1 := eq552 (σ x) (σ y)
       grind)
    | (have r₁ := eq692
       have r₂ := eq552 x y
       grind)
    | (have r₁ := eq692
       have r₂ := eq552 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq692
       have r₂ := eq552 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq692 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq692
  have eq710 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq709
  have eq726 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq710
       grind)
    | exact superpose eq710 eq16
    | exact resolve eq16 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq727 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq726
       have r₂ := eq81 x
       grind)
    | exact resolve eq726 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq728 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq727
       grind)
    | exact superpose eq727 eq16
    | exact resolve eq16 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq727
       grind)
    | exact superpose eq727 eq10
    | exact resolve eq10 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq769 : x = y := by
    first
    | (have i₁ := eq729
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq729
    | exact resolve eq729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq770 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq728
       have i₂ := eq81 x
       grind)
    | exact superpose eq81 eq728
    | exact resolve eq728 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq728
  have eq771 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq770
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq770
    | exact resolve eq770 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq770
  have eq772 : False := by grind
  exact eq772

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq39 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq125 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq621 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq125
    | (have j0 := eq125 (σ X1) (σ X0)
       grind)
    | exact resolve eq125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq3221 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq74 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq74 (σ X1) X1
       grind)
    | exact resolve eq13 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3228 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3229 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3230 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq3231 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq3234 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3229 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3229
    | (have j0 := eq3229 X0
       grind)
    | exact resolve eq3229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3279 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq3234 X0
       grind)
    | exact superpose eq3234 eq39
    | (have j1 := eq3234 X0
       grind)
    | exact resolve eq39 eq3234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3234
  have eq3296 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3279 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3279
    | (have j0 := eq3279 X0
       grind)
    | exact resolve eq3279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq3297 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3296 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3300 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3297 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3297
    | exact resolve eq3297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3297 X0
       grind)
    | exact superpose eq3297 eq11
    | exact resolve eq11 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297
  have eq3373 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3300 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq3300
    | exact resolve eq3300 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300
  have eq3633 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3373 X0
       grind)
    | exact superpose eq3373 eq11
    | exact resolve eq11 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3707 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3633 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3633
    | exact resolve eq3633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633
  have eq3777 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq3707 (τ X0)
       grind)
    | exact superpose eq3707 eq35
    | exact resolve eq35 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3824 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3777 X0
       have i₂ := eq3373 X0
       grind)
    | exact superpose eq3373 eq3777
    | exact resolve eq3777 eq3373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373 eq3777
  have eq4381 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4404 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4381 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4381
    | exact resolve eq4381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4381
  have eq4444 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4404 X0
       have i₂ := eq3707 X0
       grind)
    | exact superpose eq3707 eq4404
    | exact resolve eq4404 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4404
  have eq4465 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4444
  have eq33984 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq3231 (σ X0) X1
       grind)
    | exact superpose eq3231 eq24
    | (have j1 := eq3231 (σ X0) X1
       grind)
    | exact resolve eq24 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3231
  have eq34082 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33984 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33984
    | (have j0 := eq33984 X0 X1
       grind)
    | exact resolve eq33984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33984
  have eq34170 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34082 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34082
    | (have j0 := eq34082 X0 X1
       grind)
    | exact resolve eq34082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34082
  have eq34249 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34170 X0 X1
       have i₂ := eq3328 X0
       grind)
    | exact superpose eq3328 eq34170
    | (have j0 := eq34170 X0 X1
       grind)
    | exact resolve eq34170 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34170
  have eq34307 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34249 X0 X1
       have i₂ := eq3707 X0
       grind)
    | exact superpose eq3707 eq34249
    | (have j0 := eq34249 X0 X1
       grind)
    | exact resolve eq34249 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34249
  have eq34355 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34307 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34307
    | (have j0 := eq34307 X0 X1
       grind)
    | exact resolve eq34307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34307
  have eq38532 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34355 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34355
    | (have j0 := eq34355 X1 (τ X0)
       grind)
    | exact resolve eq34355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38604 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq34355 X1 X0
       grind)
    | exact superpose eq34355 eq11
    | (have j1 := eq34355 X1 X0
       grind)
    | exact resolve eq11 eq34355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34355
  have eq39162 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq621 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq621
    | (have j0 := eq621 (τ X0) (τ X1)
       grind)
    | exact resolve eq621 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq39248 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39162 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq39162
    | (have j0 := eq39162 X0 X1
       grind)
    | exact resolve eq39162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39162
  have eq39313 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39248 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq39248
    | (have j0 := eq39248 X0 X1
       grind)
    | exact resolve eq39248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39248
  have eq39373 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39313 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39313
    | (have j0 := eq39313 X0 X1
       grind)
    | exact resolve eq39313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39313
  have eq39428 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39373 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39373
    | (have j0 := eq39373 X0 X1
       grind)
    | exact resolve eq39373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39373
  have eq39474 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39428 X0 X1
       have i₂ := eq3328 (σ (τ X1))
       grind)
    | exact superpose eq3328 eq39428
    | (have j0 := eq39428 X0 X1
       grind)
    | exact resolve eq39428 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328 eq39428
  have eq39518 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39474 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq39474
    | (have j0 := eq39474 X0 X1
       grind)
    | exact resolve eq39474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39474
  have eq39560 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39518 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq39518
    | (have j0 := eq39518 X0 X1
       grind)
    | exact resolve eq39518 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq39518
  have eq39594 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39560 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq39560
    | (have j0 := eq39560 X0 X1
       grind)
    | exact resolve eq39560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39560
  have eq39623 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39594 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39594
    | (have j0 := eq39594 X0 X1
       grind)
    | exact resolve eq39594 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39594
  have eq39651 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39623 X0 X1
       have i₂ := eq3707 X1
       grind)
    | exact superpose eq3707 eq39623
    | (have j0 := eq39623 X0 X1
       grind)
    | exact resolve eq39623 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707 eq39623
  have eq41956 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38532 X1 (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq38532
    | (have j0 := eq38532 X0 (τ X1)
       grind)
    | exact resolve eq38532 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq38532
  have eq42197 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41956 X0 X1
       have i₂ := eq3824 X1
       grind)
    | exact superpose eq3824 eq41956
    | (have j0 := eq41956 X0 X1
       grind)
    | exact resolve eq41956 eq3824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824 eq41956
  have eq42301 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42197 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq42197
    | (have j0 := eq42197 X0 X1
       grind)
    | exact resolve eq42197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42197
  have eq42392 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42301 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq42301
    | (have j0 := eq42301 X0 X1
       grind)
    | exact resolve eq42301 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42301
  have eq42853 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq42392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42392
  have eq45334 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38604 y x
       grind)
    | exact superpose eq38604 eq16
    | (have j1 := eq38604 y x
       grind)
    | exact resolve eq16 eq38604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38604
  have eq46341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45334
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq45334
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq45334 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45334
  have eq46344 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq46341
  have eq46345 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq46344
  have eq46358 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq42853 y x
       have i₂ := eq46345
       grind)
    | exact superpose eq46345 eq42853
    | (have j0 := eq42853 y x
       grind)
    | exact resolve eq42853 eq46345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42853
  have eq46359 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq46358
  have eq46360 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq46359
  have eq47929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4465 x
       have i₂ := eq46360
       grind)
    | exact superpose eq46360 eq4465
    | exact resolve eq4465 eq46360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46360
  have eq47963 : (σ y) = (σ (M.op x x)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq47929
       have r₂ := eq16
       grind)
    | exact resolve eq47929 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47929
  have eq47996 : (M.op x x) = (τ (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq47963
       grind)
    | exact superpose eq47963 eq10
    | exact resolve eq10 eq47963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47963
  have eq48145 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq47996
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq47996
    | exact resolve eq47996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47996
  have eq48718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq4465 x
       have i₂ := eq48145
       grind)
    | exact superpose eq48145 eq4465
    | exact resolve eq4465 eq48145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48145
  have eq48752 : (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq48718
       have r₂ := eq16
       grind)
    | exact resolve eq48718 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48718
  have eq48774 : (k y x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq48752
       grind)
    | exact superpose eq48752 eq11
    | exact resolve eq11 eq48752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48752
  have eq48957 : x = (k y x) := by
    first
    | (have i₁ := eq48774
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq48774
    | exact resolve eq48774 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48774
  have eq49176 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq39651 y x
       have i₂ := eq48957
       grind)
    | exact superpose eq48957 eq39651
    | (have j0 := eq39651 y x
       grind)
    | exact resolve eq39651 eq48957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39651 eq48957
  have eq49177 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq49176
  have eq53656 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49177
       grind)
    | exact superpose eq49177 eq16
    | exact resolve eq16 eq49177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49177
  have eq53729 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq53656
       have i₂ := eq46345
       grind)
    | exact superpose eq46345 eq53656
    | exact resolve eq53656 eq46345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46345 eq53656
  have eq53732 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq53729
  have eq53733 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq53732
  have eq54278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4465 x
       have i₂ := eq53733
       grind)
    | exact superpose eq53733 eq4465
    | exact resolve eq4465 eq53733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53733
  have eq54315 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq54278
       have r₂ := eq16
       grind)
    | exact resolve eq54278 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54278
  have eq54350 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq54315
       grind)
    | exact superpose eq54315 eq10
    | exact resolve eq10 eq54315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54315
  have eq54507 : y = (M.op x x) := by
    first
    | (have i₁ := eq54350
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq54350
    | exact resolve eq54350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54350
  have eq55234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4465 x
       have i₂ := eq54507
       grind)
    | exact superpose eq54507 eq4465
    | exact resolve eq4465 eq54507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465 eq54507
  have eq55272 : False := by grind
  exact eq55272
