import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq140 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq49 X0 X1
       grind)
    | exact resolve eq12 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq146 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       grind)
    | (have r₁ := eq140 X0 X1
       have r₂ := eq39 X0
       grind)
    | exact resolve eq140 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq153 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq146
    | (have j0 := eq146 X0 X1
       grind)
    | exact resolve eq146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq155 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq156 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       have j1 := eq143 X0 X1
       grind)
    | (have r₁ := eq155 X0 X1
       have r₂ := eq143 X0 X1
       grind)
    | (have r₁ := eq155 (M.op X0 X0) (k X1 X0)
       have r₂ := eq143 X0 X1
       grind)
    | (have r₁ := eq155 (k X1 X0) (M.op X0 X0)
       have r₂ := eq143 X0 X1
       grind)
    | exact resolve eq155 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq155
  have eq652 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq156 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq156
    | exact resolve eq156 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq156 x y
       grind)
    | exact superpose eq156 eq16
    | (have j1 := eq156 x y
       grind)
    | exact resolve eq16 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq678 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq652
    | (have j0 := eq652 X0 X1
       grind)
    | exact resolve eq652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq652
  have eq683 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq678
    | exact resolve eq678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq3143 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq660
       have i₂ := eq683 x y
       grind)
    | exact superpose eq683 eq660
    | (have j1 := eq683 (σ x) (σ y)
       grind)
    | (have r₁ := eq660
       have r₂ := eq683 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq660
       have r₂ := eq683 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq660 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq683
  have eq3146 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3143
  have eq3245 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3146
       grind)
    | exact superpose eq3146 eq10
    | exact resolve eq10 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146
  have eq3289 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3245
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3245
    | exact resolve eq3245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq3290 : x = y := by grind
  clear eq3289
  have eq3292 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3290
       grind)
    | exact superpose eq3290 eq16
    | exact resolve eq16 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3293 : False := by grind
  exact eq3293

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  clear eq43
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq86 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq87 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq109 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq87
    | exact resolve eq87 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq115 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq110 sF2
       grind)
    | exact superpose eq110 eq49
    | exact resolve eq49 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq116 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq115
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq115
    | exact resolve eq115 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq188 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq104
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq104
    | exact resolve eq104 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq189 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq188
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq188
    | exact resolve eq188 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq279 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq110 (τ X0)
       grind)
    | exact superpose eq110 eq34
    | exact resolve eq34 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq290 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq279
    | exact resolve eq279 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq292 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq290
    | exact resolve eq290 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq290
  have eq325 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq381 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq326 eq14
    | exact resolve eq14 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq471 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq330 (σ X0)
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq330
    | exact resolve eq330 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq544 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0) X0 X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y x X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X1 X0) X1 X2 (M.op X0 X0)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 (M.op X0 X1) X1
       have i₂ := eq55 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq16
    | exact resolve eq16 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq851 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq119
  have eq985 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq686 X0
       grind)
    | exact superpose eq686 eq53
    | exact resolve eq53 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq851 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq851
    | (have j0 := eq851 X0 x
       grind)
    | exact resolve eq851 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq3984 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq558
    | exact resolve eq558 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4031 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3984 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3984
    | (have j0 := eq3984 y x
       grind)
    | exact resolve eq3984 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4033 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq3984
    | (have j0 := eq3984 (σ y) (σ x)
       grind)
    | exact resolve eq3984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq4099 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq4033 eq14
    | exact resolve eq14 eq4033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4303 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq554 (M.op y X0) X0
       have i₂ := eq55 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq55 eq554
    | exact resolve eq554 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq4511 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq561 X0 X0 X2 X3 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq561
    | exact resolve eq561 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq4544 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq4099 sF3
       have i₂ := eq53 sF3
       grind)
    | exact superpose eq53 eq4099
    | exact resolve eq4099 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099
  have eq5379 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1033 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1033
    | (have j0 := eq1033 y
       grind)
    | exact resolve eq1033 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq5405 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5379
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq5379
    | exact resolve eq5379 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq5379
  have eq5424 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5405
    | exact resolve eq5405 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5405
  have eq5433 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5424
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq5424
    | exact resolve eq5424 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424
  have eq5441 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq5433
    | exact resolve eq5433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5433
  have eq7182 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq28 eq357
    | exact resolve eq357 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq7220 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq39 eq7182
    | (have j0 := eq7182 X0
       grind)
    | exact resolve eq7182 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7182
  have eq7327 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq544
    | exact resolve eq544 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16780 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq331 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq558 X1 X0 X1
       grind)
    | exact superpose eq558 eq331
    | exact resolve eq331 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq16796 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq381 eq331
    | exact resolve eq331 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq16974 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq16796 eq331
    | exact resolve eq331 eq16796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16796
  have eq20647 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16974 sF3
       have i₂ := eq53 sF3
       grind)
    | exact superpose eq53 eq16974
    | exact resolve eq16974 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16974
  have eq20697 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20647 eq4544
    | exact resolve eq4544 eq20647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4544
  have eq25467 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4511 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq53 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq4511
    | exact resolve eq4511 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4511
  have eq25681 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25467 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq25467
    | exact resolve eq25467 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26159 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq7327 X1 X0
       grind)
    | exact superpose eq7327 eq14
    | exact resolve eq14 eq7327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32995 : y = (M.op (M.op x y) (M.op y x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq325
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq325
    | exact resolve eq325 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq325
  have eq36118 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7327 X2 X1
       have i₂ := eq583 X1 X2 X0
       grind)
    | (have i₁ := eq7327 X1 X1
       have i₂ := eq583 X1 X1 X1
       grind)
    | exact superpose eq583 eq7327
    | exact resolve eq7327 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq38325 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X1 x (M.op X1 x)
       have i₂ := eq36118 X1 X1 x
       grind)
    | exact superpose eq36118 eq544
    | exact resolve eq544 eq36118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq36118
  have eq44866 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq25681 X0 y
       have i₂ := eq4303 X0
       grind)
    | exact superpose eq4303 eq25681
    | exact resolve eq25681 eq4303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq44876 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7327 X0 X1
       have i₂ := eq25681 X0 X1
       grind)
    | exact superpose eq25681 eq7327
    | exact resolve eq7327 eq25681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7327
  have eq46960 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq5441 eq55
    | exact resolve eq55 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5441
  have eq47017 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq46960
       have i₂ := eq25681 sF2 sF3
       grind)
    | exact superpose eq25681 eq46960
    | exact resolve eq46960 eq25681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46960
  have eq49460 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq559 X0 X1 X2 X3
       have i₂ := eq25681 X0 X1
       grind)
    | exact superpose eq25681 eq559
    | exact resolve eq559 eq25681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq50086 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X1 X1
       have i₂ := eq49460 X1 X0 X0 X1
       grind)
    | exact superpose eq49460 eq52
    | exact resolve eq52 eq49460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq50103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq331 (M.op X2 X1) X3 (M.op X1 (M.op X0 X1))
       have i₂ := eq49460 X1 X0 X2 (M.op X2 X1)
       grind)
    | exact superpose eq49460 eq331
    | exact resolve eq331 eq49460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq49460
  have eq50271 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50103 X0 X1 X2 X3
       have i₂ := eq25681 X1 X2
       grind)
    | exact superpose eq25681 eq50103
    | exact resolve eq50103 eq25681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50103
  have eq57082 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38325 X0 X1
       have i₂ := eq25681 X1 X0
       grind)
    | exact superpose eq25681 eq38325
    | exact resolve eq38325 eq25681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38325
  have eq57324 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57082 X1 X2
       have i₂ := eq50086 X1 X2 X0
       grind)
    | (have i₁ := eq57082 X0 (M.op X2 X0)
       have i₂ := eq50086 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq50086 eq57082
    | exact resolve eq57082 eq50086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50086 eq57082
  have eq150753 : y = (M.op x (M.op y x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44866 eq32995
    | exact resolve eq32995 eq44866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32995 eq44866
  have eq161071 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq47017 eq44876
    | exact resolve eq44876 eq47017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47017
  have eq161209 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq161071
    | exact resolve eq161071 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161071
  have eq161236 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq161209 eq96
    | exact resolve eq96 eq161209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq173720 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44876 x y
       have i₂ := eq150753
       grind)
    | exact superpose eq150753 eq44876
    | exact resolve eq44876 eq150753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173870 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq173720
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq173720
    | exact resolve eq173720 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173720
  have eq173910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173870 eq161209
    | exact resolve eq161209 eq173870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161209
  have eq173911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173870 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq173870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173870
  have eq173923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq173911
    | exact resolve eq173911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173911
  have eq173924 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq173910
       have r₂ := eq27
       grind)
    | exact resolve eq173910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173910
  have eq173936 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq173923
       have r₂ := eq27
       grind)
    | exact resolve eq173923 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173923
  have eq173940 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq173936
    | exact resolve eq173936 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173936
  have eq174775 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173940 eq189
    | exact resolve eq189 eq173940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174843 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173940 eq53
    | exact resolve eq53 eq173940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173940
  have eq175704 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173924 eq174843
    | exact resolve eq174843 eq173924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173924
  have eq175743 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq174843 eq16780
    | exact resolve eq16780 eq174843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174843
  have eq175832 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq175704
  have eq175923 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq175832 eq20697
    | exact resolve eq20697 eq175832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175832
  have eq178987 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7220 y
       have i₂ := eq161236
       grind)
    | exact superpose eq161236 eq7220
    | (have j0 := eq7220 y
       grind)
    | exact resolve eq7220 eq161236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7220 eq161236
  have eq179300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq178987
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq178987
    | exact resolve eq178987 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178987
  have eq179326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq179300
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179300
    | exact resolve eq179300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179300
  have eq179341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq179326
    | exact resolve eq179326 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179326
  have eq179351 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq179341
       have r₂ := eq27
       grind)
    | exact resolve eq179341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179341
  have eq179356 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq179351
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179351
    | exact resolve eq179351 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179351
  have eq183632 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq179356
       grind)
    | exact superpose eq179356 eq53
    | exact resolve eq53 eq179356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183696 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y x)) (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq26159 y y x
       have i₂ := eq179356
       grind)
    | exact superpose eq179356 eq26159
    | exact resolve eq26159 eq179356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26159 eq179356
  have eq183756 : y = (M.op x (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq183696 x
       have i₂ := eq50271 y x y x
       grind)
    | exact superpose eq50271 eq183696
    | exact resolve eq183696 eq50271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50271 eq183696
  have eq193404 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16780 y x y
       have i₂ := eq183632
       grind)
    | exact superpose eq183632 eq16780
    | exact resolve eq16780 eq183632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183632
  have eq195826 : y = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq183756
       have i₂ := eq193404
       grind)
    | exact superpose eq193404 eq183756
    | exact resolve eq183756 eq193404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183756 eq193404
  have eq195952 : y = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq195826
  have eq195981 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq195952
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq195952
    | exact resolve eq195952 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195952
  have eq196076 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq195981 eq25681
    | exact resolve eq25681 eq195981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196145 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20647 eq196076
    | exact resolve eq196076 eq20647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196076
  have eq242278 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq175743 eq174775
    | exact resolve eq174775 eq175743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174775 eq175743
  have eq242564 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq242278
  have eq242587 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq242564
    | exact resolve eq242564 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242564
  have eq242749 : (M.op (M.op x x) (M.op x x)) = (M.op y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25681 y y
       have i₂ := eq242587
       grind)
    | exact superpose eq242587 eq25681
    | exact resolve eq25681 eq242587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25681 eq242587
  have eq242829 : x = (M.op y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq242749
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq242749
    | exact resolve eq242749 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242749
  have eq243867 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25467 y (M.op x x)
       have i₂ := eq242829
       grind)
    | exact superpose eq242829 eq25467
    | exact resolve eq25467 eq242829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242829
  have eq243953 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq243867
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq243867
    | exact resolve eq243867 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243867
  have eq244029 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq243953
       grind)
    | exact superpose eq243953 eq117
    | exact resolve eq117 eq243953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq243953
  have eq244329 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq244029
    | exact resolve eq244029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244029
  have eq249854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq244329 eq175923
    | exact resolve eq175923 eq244329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175923 eq244329
  have eq250040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq249854
  have eq250089 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq250040
       have r₂ := eq27
       grind)
    | exact resolve eq250040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250040
  have eq250254 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op (M.op x y) (M.op x X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57324 y x X0
       have i₂ := eq250089
       grind)
    | exact superpose eq250089 eq57324
    | exact resolve eq57324 eq250089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57324 eq250089
  have eq283334 : y = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq250254 (M.op y x)
       have i₂ := eq150753
       grind)
    | exact superpose eq150753 eq250254
    | exact resolve eq250254 eq150753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250254
  have eq283568 : y = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq283334
  have eq283632 : y = (M.op x (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4031 eq283568
    | exact resolve eq283568 eq4031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283568
  have eq322242 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq25467 x (M.op y y)
       have i₂ := eq283632
       grind)
    | exact superpose eq283632 eq25467
    | exact resolve eq25467 eq283632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25467 eq283632
  have eq358801 : y = (M.op x (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq150753
       have i₂ := eq322242
       grind)
    | exact superpose eq322242 eq150753
    | exact resolve eq150753 eq322242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150753 eq322242
  have eq358981 : y = (M.op x (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq358801
  have eq359014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq358981
       have i₂ := eq53 x
       grind)
    | exact superpose eq53 eq358981
    | exact resolve eq358981 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358981
  have eq359188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq359014 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq359014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359014
  have eq359209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq359188
    | exact resolve eq359188 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359188
  have eq359222 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq359209
       have r₂ := eq27
       grind)
    | exact resolve eq359209 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359209
  have eq359226 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq359222
    | exact resolve eq359222 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359222
  have eq359227 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq359226
  have eq359601 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq359227 eq53
    | exact resolve eq53 eq359227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359227
  have eq360057 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq195981 eq359601
    | exact resolve eq359601 eq195981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360115 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq359601 eq16780
    | exact resolve eq16780 eq359601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16780 eq359601
  have eq360240 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq360057
  have eq360354 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq360240 eq20697
    | exact resolve eq20697 eq360240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20697 eq360240
  have eq360772 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq360354 eq189
    | exact resolve eq189 eq360354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq360354
  have eq362528 : y = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq360772
       grind)
    | exact superpose eq360772 eq55
    | exact resolve eq55 eq360772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq360772
  have eq362666 : y = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq362528
       have i₂ := eq686 sF4
       grind)
    | exact superpose eq686 eq362528
    | exact resolve eq362528 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq362528
  have eq362743 : y = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20647 eq362666
    | exact resolve eq362666 eq20647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20647 eq362666
  have eq364354 : y = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq196145 eq362743
    | exact resolve eq362743 eq196145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196145 eq362743
  have eq364751 : y = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq364354
  have eq367432 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq360115 eq195981
    | exact resolve eq195981 eq360115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195981 eq360115
  have eq367611 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq367432
  have eq367921 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq367611 eq53
    | exact resolve eq53 eq367611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367611
  have eq368593 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq367921 eq364751
    | exact resolve eq364751 eq367921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364751 eq367921
  have eq368765 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq368593
  have eq368848 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq368765
    | exact resolve eq368765 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368765
  have eq368849 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq368848
  have eq368884 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq368849 eq4033
    | exact resolve eq4033 eq368849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4033
  have eq369053 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq368884
    | exact resolve eq368884 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368884
  have eq369629 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq369053 eq53
    | exact resolve eq53 eq369053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq369053
  have eq369904 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq368849 eq369629
    | exact resolve eq369629 eq368849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369629
  have eq370200 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq369904
  have eq371719 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq370200 eq44876
    | exact resolve eq44876 eq370200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44876 eq370200
  have eq371811 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq371719
    | exact resolve eq371719 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371719
  have eq372760 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq368849 eq371811
    | exact resolve eq371811 eq368849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368849 eq371811
  have eq373000 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq372760
  have eq374216 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq373000 eq985
    | exact resolve eq985 eq373000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq373000
  have eq374422 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq374216
    | exact resolve eq374216 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq374216
  have eq374455 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq374422
    | exact resolve eq374422 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq374422
  have eq374465 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq374455
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq374455
    | exact resolve eq374455 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374455
  have eq374466 : x = (M.op x y) ∨ x = y := by grind
  clear eq374465
  have eq374472 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq374466 eq20
    | exact resolve eq20 eq374466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374635 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq374466 eq4031
    | exact resolve eq4031 eq374466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031 eq374466
  have eq374824 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq374635
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq374635
    | exact resolve eq374635 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374635
  have eq374974 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq374472
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq374472
    | exact resolve eq374472 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374472
  have eq375237 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq374974 eq26
    | exact resolve eq26 eq374974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374974
  have eq375787 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq471 y
       have i₂ := eq374824
       grind)
    | exact superpose eq374824 eq471
    | exact resolve eq471 eq374824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq374824
  have eq375995 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq375787
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq375787
    | exact resolve eq375787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375787
  have eq376065 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq375995
    | exact resolve eq375995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375995
  have eq378820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq376065 eq375237
    | exact resolve eq375237 eq376065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375237 eq376065
  have eq378943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq378820
  have eq378972 : x = y := by
    first
    | (have r₁ := eq378943
       have r₂ := eq27
       grind)
    | exact resolve eq378943 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378943
  have eq378982 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq378972
       grind)
    | exact superpose eq378972 eq18
    | exact resolve eq18 eq378972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq378983 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq378972
       grind)
    | exact superpose eq378972 eq24
    | exact resolve eq24 eq378972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq378972
  have eq379544 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq378983
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq378983
    | exact resolve eq378983 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq378983
  have eq379611 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq379544 eq26
    | exact resolve eq26 eq379544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq379544
  have eq380624 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq379611 eq116
    | exact resolve eq116 eq379611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq379611
  have eq380912 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq380624
       have i₂ := eq378982
       grind)
    | exact superpose eq378982 eq380624
    | exact resolve eq380624 eq378982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378982 eq380624
  have eq385420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq380912 eq15
    | exact resolve eq15 eq380912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380912
  have eq385956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq385420
    | exact resolve eq385420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq385420
  have eq386131 : False := by grind
  exact eq386131

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq21 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq21
    | exact resolve eq21 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq21 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq34 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq35
    | exact resolve eq35 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35
  have eq37 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq36
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq52 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq37 (τ X0)
       grind)
    | exact superpose eq37 eq18
    | exact resolve eq18 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq55 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq56 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq158 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq159 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq158 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq158
    | exact resolve eq158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq186 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq60
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq23
    | (have j1 := eq60 X0 X0
       grind)
    | exact resolve eq23 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq213 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq245 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq20 X1 X1 X0 X2
       grind)
    | exact superpose eq20 eq31
    | exact resolve eq31 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31
  have eq334 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq21 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq245
    | exact resolve eq245 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq245
  have eq511 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq159 (τ X0)
       grind)
    | exact superpose eq159 eq18
    | exact resolve eq18 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq514 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq511 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq511
    | exact resolve eq511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq15198 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq213 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq213
    | (have j0 := eq213 (τ X0) X1
       grind)
    | exact resolve eq213 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq213
  have eq15327 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15198 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15198
    | (have j0 := eq15198 X0 X1
       grind)
    | exact resolve eq15198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15198
  have eq15350 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15327 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15327
    | (have j0 := eq15327 X0 X1
       grind)
    | exact resolve eq15327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15327
  have eq15423 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq334 (k X0 X0) X0
       have i₂ := eq15350 X0 (k X0 X0)
       grind)
    | exact superpose eq15350 eq334
    | (have j1 := eq15350 X0 x
       grind)
    | exact resolve eq334 eq15350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15350
  have eq15648 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0) (k X0 X0)
       have i₂ := eq15423 X0
       grind)
    | exact superpose eq15423 eq23
    | (have j1 := eq15423 X0
       grind)
    | exact resolve eq23 eq15423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15423
  have eq15743 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15648 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq15648 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq15648 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15648
  have eq16047 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq15743 (σ X0)
       grind)
    | exact superpose eq15743 eq15
    | exact resolve eq15 eq15743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16053 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0 X0
       have i₂ := eq15743 (τ X0)
       grind)
    | exact superpose eq15743 eq73
    | exact resolve eq73 eq15743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq16077 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16053 X0
       have i₂ := eq15743 X0
       grind)
    | exact superpose eq15743 eq16053
    | exact resolve eq16053 eq15743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16053
  have eq16083 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16047 X0
       have i₂ := eq15743 X0
       grind)
    | exact superpose eq15743 eq16047
    | exact resolve eq16047 eq15743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15743 eq16047
  have eq16710 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq334 (σ X0) (σ X0)
       have i₂ := eq16083 X0
       grind)
    | exact superpose eq16083 eq334
    | exact resolve eq334 eq16083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43456 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))) X1
       have i₂ := eq514 (τ X0)
       grind)
    | exact superpose eq514 eq186
    | (have j0 := eq186 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))) X1
       grind)
    | exact resolve eq186 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq43498 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (k X0 (σ (σ (σ (σ (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))))) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43456 X0 X1
       have i₂ := eq16077 (τ (τ (τ X0)))
       grind)
    | exact superpose eq16077 eq43456
    | (have j0 := eq43456 X0 X1
       grind)
    | exact resolve eq43456 eq16077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43456
  have eq43551 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43498 X0 X1
       have i₂ := eq11 (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))
       grind)
    | exact superpose eq11 eq43498
    | (have j0 := eq43498 X0 X1
       grind)
    | exact resolve eq43498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43498
  have eq43598 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43551 X0 X1
       have i₂ := eq514 X0
       grind)
    | exact superpose eq514 eq43551
    | (have j0 := eq43551 X0 X1
       grind)
    | exact resolve eq43551 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43551
  have eq43638 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43598 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq43598
    | (have j0 := eq43598 X0 X1
       grind)
    | exact resolve eq43598 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43598
  have eq43669 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))))) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43638 X0 X1
       have i₂ := eq16077 (τ (τ (τ X0)))
       grind)
    | exact superpose eq16077 eq43638
    | (have j0 := eq43638 X0 X1
       grind)
    | exact resolve eq43638 eq16077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43638
  have eq43700 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43669 X0 X1
       have i₂ := eq11 (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))
       grind)
    | exact superpose eq11 eq43669
    | (have j0 := eq43669 X0 X1
       grind)
    | exact resolve eq43669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43669
  have eq43725 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43700 X0 X1
       have i₂ := eq514 X0
       grind)
    | exact superpose eq514 eq43700
    | (have j0 := eq43700 X0 X1
       grind)
    | exact resolve eq43700 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43700
  have eq43739 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43725 X0 X1
       have i₂ := eq16083 X1
       grind)
    | exact superpose eq16083 eq43725
    | (have j0 := eq43725 X0 X1
       grind)
    | exact resolve eq43725 eq16083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16083 eq43725
  have eq43743 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))))) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43739 X0 X1
       have i₂ := eq16077 (τ (τ (τ X0)))
       grind)
    | exact superpose eq16077 eq43739
    | (have j0 := eq43739 X0 X1
       grind)
    | exact resolve eq43739 eq16077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43739
  have eq43745 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43743 X0 X1
       have i₂ := eq11 (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))
       grind)
    | exact superpose eq11 eq43743
    | (have j0 := eq43743 X0 X1
       grind)
    | exact resolve eq43743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43743
  have eq43746 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43745 X0 X1
       have i₂ := eq514 X0
       grind)
    | exact superpose eq514 eq43745
    | (have j0 := eq43745 X0 X1
       grind)
    | exact resolve eq43745 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq43745
  have eq43747 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43746 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq43746 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq43746 (M.op (σ (M.op X1 X1)) X0) X1
       have r₂ := eq12 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq43746 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43746
  have eq44097 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43747 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43747
    | (have j0 := eq43747 X1 (τ X0)
       grind)
    | exact resolve eq43747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq43747 (σ X0) X1
       grind)
    | exact superpose eq43747 eq15
    | (have j1 := eq43747 (σ X0) X1
       grind)
    | exact resolve eq15 eq43747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43747
  have eq44259 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44097 X0 X1
       have i₂ := eq16077 X0
       grind)
    | exact superpose eq16077 eq44097
    | (have j0 := eq44097 X0 X1
       grind)
    | exact resolve eq44097 eq16077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16077 eq44097
  have eq44286 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44259 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq44259
    | (have j0 := eq44259 X0 X1
       grind)
    | exact resolve eq44259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44259
  have eq44404 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq44286 X1 (τ X0)
       grind)
    | exact superpose eq44286 eq18
    | (have j1 := eq44286 X1 (τ X0)
       grind)
    | exact resolve eq18 eq44286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq44286
  have eq50020 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44404 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44404
    | exact resolve eq44404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44404
  have eq50240 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50020 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq50020
    | (have j0 := eq50020 X0 X1
       grind)
    | exact resolve eq50020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50020
  have eq89638 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44173 x y
       grind)
    | exact superpose eq44173 eq16
    | (have j1 := eq44173 x y
       grind)
    | exact resolve eq16 eq44173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44173
  have eq90209 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq89638
       have i₂ := eq50240 x y
       grind)
    | exact superpose eq50240 eq89638
    | (have j1 := eq50240 x y
       grind)
    | (have r₁ := eq89638
       have r₂ := eq50240 x y
       grind)
    | exact resolve eq89638 eq50240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50240 eq89638
  have eq90212 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq90209
  have eq91891 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq90212
       grind)
    | exact superpose eq90212 eq10
    | exact resolve eq10 eq90212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90212
  have eq92035 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq91891
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq91891
    | exact resolve eq91891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91891
  have eq92036 : x = (M.op y y) := by grind
  clear eq92035
  have eq92143 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16710 y
       have i₂ := eq92036
       grind)
    | exact superpose eq92036 eq16710
    | exact resolve eq16710 eq92036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16710
  have eq92183 : x = (M.op x y) := by
    first
    | (have i₁ := eq334 y y
       have i₂ := eq92036
       grind)
    | exact superpose eq92036 eq334
    | exact resolve eq334 eq92036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq92036
  have eq100593 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92143
       grind)
    | exact superpose eq92143 eq16
    | exact resolve eq16 eq92143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92143
  have eq100833 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq100593
       have i₂ := eq92183
       grind)
    | exact superpose eq92183 eq100593
    | exact resolve eq100593 eq92183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92183 eq100593
  have eq100834 : False := by grind
  exact eq100834

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  clear eq36
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq60 X0
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq86 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  clear eq45
  have eq93 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq86
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq149 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq321 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 (M.op X0 X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq61
    | (have r₁ := eq61 X0 X0 X0
       have r₂ := eq60 X0
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq357 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq59
    | exact resolve eq59 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq455 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq60 (σ X0)
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq60
    | (have j1 := eq80 X0 X0
       grind)
    | exact resolve eq60 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq465 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq468 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq3145 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X0 X1
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq357
    | exact resolve eq357 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq3173 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3145 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3145
    | (have j0 := eq3145 y x
       grind)
    | exact resolve eq3145 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3771 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq468 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq468
    | (have j0 := eq468 (τ X0)
       grind)
    | exact resolve eq468 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq468
  have eq3793 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3771 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3771
    | (have j0 := eq3771 X0
       grind)
    | exact resolve eq3771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771
  have eq3804 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3793 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3793
    | (have j0 := eq3793 X0
       grind)
    | exact resolve eq3793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq4024 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq360 X0 X0 X2 X3 X1
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq360
    | exact resolve eq360 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq19368 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4024 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq60 (M.op X0 X1)
       grind)
    | exact superpose eq60 eq4024
    | exact resolve eq4024 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq4024
  have eq24513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq24514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq24513
    | exact resolve eq24513 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24513
  have eq24525 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq24514
       have r₂ := eq28
       grind)
    | exact resolve eq24514 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24514
  have eq24542 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24525 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq24525
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq24525
       grind)
    | exact resolve eq13 eq24525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24525
  have eq24562 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24542
  have eq24571 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24562 eq56
    | exact resolve eq56 eq24562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24562
  have eq24596 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq24571
    | exact resolve eq24571 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24571
  have eq24599 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq24596
       have r₂ := eq13 x y
       grind)
    | exact resolve eq24596 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24596
  have eq24620 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24599 eq65
    | exact resolve eq65 eq24599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24599
  have eq25606 : (τ (σ x)) = (k x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24620 eq56
    | exact resolve eq56 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq24620
  have eq25630 : x = (k x y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq25606
    | exact resolve eq25606 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25606
  have eq25631 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq25630
  have eq25650 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq25631
       grind)
    | exact superpose eq25631 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq25631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25631
  have eq25651 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq25650
  have eq25654 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25651
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25651
    | exact resolve eq25651 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25651
  have eq26014 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3145 x y
       have i₂ := eq25654
       grind)
    | exact superpose eq25654 eq3145
    | exact resolve eq3145 eq25654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq28350 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25654
       have i₂ := eq26014
       grind)
    | exact superpose eq26014 eq25654
    | exact resolve eq25654 eq26014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25654 eq26014
  have eq28391 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq28350
  have eq28424 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 x x
       have i₂ := eq28391
       grind)
    | exact superpose eq28391 eq63
    | exact resolve eq63 eq28391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28391
  have eq28444 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq28424
  have eq28508 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19368 y y
       have i₂ := eq28444
       grind)
    | exact superpose eq28444 eq19368
    | exact resolve eq19368 eq28444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19368 eq28444
  have eq28512 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28508
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28508
    | exact resolve eq28508 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28508
  have eq28513 : x = (M.op x y) := by grind
  clear eq28512
  have eq28528 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28513 eq21
    | exact resolve eq21 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28600 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28513 eq3173
    | exact resolve eq3173 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq28661 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq28600
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28600
    | exact resolve eq28600 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28600
  have eq28721 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28528
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28528
    | exact resolve eq28528 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28528
  have eq28724 : x = (M.op y y) := by
    first
    | exact superpose eq28513 eq28661
    | exact resolve eq28661 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28661
  have eq28726 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28721 eq27
    | exact resolve eq27 eq28721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq28990 : y = (M.op x x) := by
    first
    | (have i₁ := eq63 y y
       have i₂ := eq28724
       grind)
    | exact superpose eq28724 eq63
    | exact resolve eq63 eq28724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq28991 : x ≠ y ∨ x = (k x x) := by
    first
    | (have i₁ := eq321 y y
       have i₂ := eq28724
       grind)
    | exact superpose eq28724 eq321
    | exact resolve eq321 eq28724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq28724
  have eq29221 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq28990
       grind)
    | exact superpose eq28990 eq93
    | exact resolve eq93 eq28990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq28990
  have eq29280 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq28721 eq29221
    | exact resolve eq29221 eq28721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29221
  have eq29288 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq29280
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29280
    | exact resolve eq29280 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29280
  have eq31258 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29288 eq149
    | exact resolve eq149 eq29288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31274 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq29288 eq3804
    | (have j0 := eq3804 (σ (M.op x y))
       grind)
    | exact resolve eq3804 eq29288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804 eq29288
  have eq31291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq28726 eq31274
    | exact resolve eq31274 eq28726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31274
  have eq31299 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq28513 eq31258
    | exact resolve eq31258 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31258
  have eq31302 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq31291
       have r₂ := eq28
       grind)
    | exact resolve eq31291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31291
  have eq31310 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq30 eq31299
    | exact resolve eq31299 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31299
  have eq31410 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq31302 eq65
    | exact resolve eq65 eq31302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq31302
  have eq31558 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31410 eq149
    | exact resolve eq149 eq31410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq31410
  have eq31606 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq28513 eq31558
    | exact resolve eq31558 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31558
  have eq31615 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq31606
    | exact resolve eq31606 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq31606
  have eq31623 : x = (k x x) ∨ x = y := by
    first
    | exact superpose eq28513 eq31615
    | exact resolve eq31615 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28513 eq31615
  have eq31628 : x = (k x x) := by
    first
    | (have r₁ := eq31623
       have r₂ := eq28991
       grind)
    | exact resolve eq31623 eq28991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28991 eq31623
  have eq31644 : x = y ∨ x = y := by
    first
    | (have i₁ := eq31310
       have i₂ := eq31628
       grind)
    | exact superpose eq31628 eq31310
    | exact resolve eq31310 eq31628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31310
  have eq31650 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq465 x
       have i₂ := eq31628
       grind)
    | exact superpose eq31628 eq465
    | (have j0 := eq465 x
       grind)
    | exact resolve eq465 eq31628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq31628
  have eq31661 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31650
  have eq31665 : x = y := by grind
  clear eq31644
  have eq31672 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31661
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31661
    | exact resolve eq31661 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31661
  have eq31691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28721 eq31672
    | exact resolve eq31672 eq28721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31672
  have eq31717 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq31665
       grind)
    | exact superpose eq31665 eq25
    | exact resolve eq25 eq31665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq31665
  have eq31966 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31717
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31717
    | exact resolve eq31717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31717
  have eq32044 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28721 eq31966
    | exact resolve eq31966 eq28721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28721 eq31966
  have eq32276 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq32044 eq28726
    | exact resolve eq28726 eq32044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28726 eq32044
  have eq32649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31691 eq32276
    | exact resolve eq32276 eq31691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31691 eq32276
  have eq32650 : False := by grind
  exact eq32650

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  clear eq36
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  clear eq45
  have eq66 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq64
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq66
    | exact resolve eq66 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq80 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ≠ X0 ∨ (M.op X1 (M.op X0 X2)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (k (M.op X1 (M.op X0 X2)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq82 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
  have eq233 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 y x
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq233 eq14
    | exact resolve eq14 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq340 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq83
    | (have j0 := eq83 (σ X0)
       grind)
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq502 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq870 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ≠ X0 ∨ (M.op X1 (M.op X0 X2)) = X0 ∨ (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (k (M.op X1 (M.op X0 X2)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 X2
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq80
    | (have j0 := eq80 X0 X1 X2
       grind)
    | exact resolve eq80 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq922 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq870
    | exact resolve eq870 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq3422 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq502
    | exact resolve eq502 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq3451 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3422 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3422
    | (have j0 := eq3422 y x
       grind)
    | exact resolve eq3422 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3453 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3422
    | (have j0 := eq3422 (σ y) (σ x)
       grind)
    | exact resolve eq3422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq3492 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op y y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3451 eq14
    | exact resolve eq14 eq3451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq3509 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3492 y
       have i₂ := eq50 y
       grind)
    | exact superpose eq50 eq3492
    | exact resolve eq3492 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492
  have eq3530 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y y)) := by
    intro X0
    first
    | exact superpose eq3509 eq14
    | exact resolve eq14 eq3509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3509
  have eq3740 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq340 X0
       grind)
    | exact superpose eq340 eq50
    | (have j1 := eq340 X0
       grind)
    | exact resolve eq50 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3754 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq4132 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq505 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq505
    | exact resolve eq505 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq7709 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq922 X0 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq922
    | (have j0 := eq922 X0 X0
       grind)
    | (have r₁ := eq922 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq922 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq7710 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7709 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7709
  have eq11055 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq247 eq239
    | exact resolve eq239 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq11166 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11055 eq239
    | exact resolve eq239 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq11600 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq11166 y
       have i₂ := eq50 y
       grind)
    | exact superpose eq50 eq11166
    | exact resolve eq11166 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11166
  have eq16107 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4132 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq4132
    | exact resolve eq4132 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132
  have eq21795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq68 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq21795
    | exact resolve eq21795 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21795
  have eq21807 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq21796
       have r₂ := eq28
       grind)
    | exact resolve eq21796 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21796
  have eq21809 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq21807
    | exact resolve eq21807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21807
  have eq21814 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21809 eq82
    | (have r₁ := eq82
       have r₂ := eq21809
       grind)
    | exact resolve eq82 eq21809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq21809
  have eq21856 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq21814
  have eq21857 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq21856
  have eq23472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21857 eq68
    | exact resolve eq68 eq21857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21857
  have eq23481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq23472
  have eq23484 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq23481
       have r₂ := eq28
       grind)
    | exact resolve eq23481 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23481
  have eq23508 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  have eq23540 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23484 eq16107
    | exact resolve eq16107 eq23484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23484
  have eq23546 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq23540
    | exact resolve eq23540 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23540
  have eq23571 : x = (M.op y y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq23546
       grind)
    | exact superpose eq23546 eq50
    | exact resolve eq50 eq23546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23584 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq23546
       grind)
    | exact superpose eq23546 eq52
    | exact resolve eq52 eq23546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23546
  have eq23615 : x = (M.op y (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11600 eq23584
    | exact resolve eq23584 eq11600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11600 eq23584
  have eq24230 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16107 y y
       have i₂ := eq23571
       grind)
    | exact superpose eq23571 eq16107
    | exact resolve eq16107 eq23571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23571
  have eq24234 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24230
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24230
    | exact resolve eq24230 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24230
  have eq24249 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24234 eq3530
    | exact resolve eq3530 eq24234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq24251 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24234 eq11055
    | exact resolve eq11055 eq24234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11055
  have eq24282 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24251
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24251
    | exact resolve eq24251 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24251
  have eq25161 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23615 eq16107
    | exact resolve eq16107 eq23615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25166 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25161
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25161
    | exact resolve eq25161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25161
  have eq25475 : y = (M.op y (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq25166
       grind)
    | exact superpose eq25166 eq50
    | exact resolve eq50 eq25166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq25166
  have eq25542 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24249
       have i₂ := eq24282
       grind)
    | exact superpose eq24282 eq24249
    | exact resolve eq24249 eq24282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24249 eq24282
  have eq25585 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25542
  have eq25594 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25585 eq24234
    | exact resolve eq24234 eq25585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24234 eq25585
  have eq25629 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25594
  have eq25634 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25629 eq28
    | exact resolve eq28 eq25629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25645 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25629 eq3453
    | exact resolve eq3453 eq25629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453
  have eq25695 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq25645
    | exact resolve eq25645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25645
  have eq25719 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25695
  have eq25784 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25629 eq25719
    | exact resolve eq25719 eq25629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25629 eq25719
  have eq25787 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25784
  have eq25898 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25787 eq60
    | exact resolve eq60 eq25787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq25787
  have eq25919 : x = (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq25898
    | exact resolve eq25898 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25898
  have eq26700 : x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25475 eq23615
    | exact resolve eq23615 eq25475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23615 eq25475
  have eq26742 : x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26700
  have eq26797 : y = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7710 y
       have i₂ := eq26742
       grind)
    | exact superpose eq26742 eq7710
    | exact resolve eq7710 eq26742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7710
  have eq26803 : y = (M.op x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq26742
       grind)
    | exact superpose eq26742 eq52
    | exact resolve eq52 eq26742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq26742
  have eq26828 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26797
  have eq27119 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq344
       have i₂ := eq26803
       grind)
    | exact superpose eq26803 eq344
    | exact resolve eq344 eq26803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26803
  have eq27174 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27119
  have eq27180 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27174
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27174
    | exact resolve eq27174 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27174
  have eq53973 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq23508 eq68
    | exact resolve eq68 eq23508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq23508
  have eq53986 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq53973
  have eq54275 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq53986
       grind)
    | exact superpose eq53986 eq81
    | (have r₁ := eq81
       have r₂ := eq53986
       grind)
    | exact resolve eq81 eq53986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq53986
  have eq54334 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq54275
  have eq54335 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq54334
  have eq56233 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25919
       have i₂ := eq54335
       grind)
    | exact superpose eq54335 eq25919
    | exact resolve eq25919 eq54335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25919 eq54335
  have eq56241 : x = (M.op x y) ∨ x = y ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq56233
  have eq56249 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq56241
       have r₂ := eq25634
       grind)
    | exact resolve eq56241 eq25634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25634 eq56241
  have eq56335 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16107 y y
       have i₂ := eq56249
       grind)
    | exact superpose eq56249 eq16107
    | exact resolve eq16107 eq56249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16107 eq56249
  have eq56356 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56335
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56335
    | exact resolve eq56335 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56335
  have eq56357 : x = (M.op x y) ∨ x = y := by grind
  clear eq56356
  have eq56374 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq56357 eq21
    | exact resolve eq21 eq56357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56677 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq56374
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq56374
    | exact resolve eq56374 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56374
  have eq56793 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq56677 eq27180
    | exact resolve eq27180 eq56677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27180
  have eq56829 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq56793
  have eq56844 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq56829
       have r₂ := eq28
       grind)
    | exact resolve eq56829 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56829
  have eq72942 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3740 x
       have i₂ := eq26828
       grind)
    | exact superpose eq26828 eq3740
    | (have j0 := eq3740 x
       grind)
    | exact resolve eq3740 eq26828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740 eq26828
  have eq73050 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72942
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72942
    | exact resolve eq72942 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72942
  have eq73083 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73050
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq73050
    | exact resolve eq73050 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73050
  have eq73105 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq73083
    | exact resolve eq73083 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73083
  have eq73106 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq73105
  have eq73112 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq73106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq73106
    | exact resolve eq73106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73106
  have eq78523 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq56677 eq73112
    | exact resolve eq73112 eq56677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56677 eq73112
  have eq78599 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq78523
  have eq78609 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq78599
       have r₂ := eq28
       grind)
    | exact resolve eq78599 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78599
  have eq78612 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq78609
  have eq79244 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq78612 eq56844
    | exact resolve eq56844 eq78612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56844 eq78612
  have eq79261 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq79244
  have eq79276 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq79261 eq30
    | exact resolve eq30 eq79261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq79261
  have eq79629 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq79276
    | exact resolve eq79276 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq79276
  have eq80351 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq79629 eq56357
    | exact resolve eq56357 eq79629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56357 eq79629
  have eq80438 : x = y := by grind
  clear eq80351
  have eq80613 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq80438
       grind)
    | exact superpose eq80438 eq19
    | exact resolve eq19 eq80438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq80614 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq80438
       grind)
    | exact superpose eq80438 eq25
    | exact resolve eq25 eq80438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq80438
  have eq80954 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq80614
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80614
    | exact resolve eq80614 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80614
  have eq81547 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq80954 eq27
    | exact resolve eq27 eq80954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq80954
  have eq81843 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq344
       have i₂ := eq80613
       grind)
    | exact superpose eq80613 eq344
    | exact resolve eq344 eq80613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq81871 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq80613
  have eq81931 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq81843
    | exact resolve eq81843 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81843
  have eq81984 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq91784 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81931 eq83
    | (have j0 := eq83 (σ x)
       grind)
    | exact resolve eq83 eq81931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81547 eq91784
    | exact resolve eq91784 eq81547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91784
  have eq91799 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq91787
       have r₂ := eq28
       grind)
    | exact resolve eq91787 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91787
  have eq91806 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81547 eq91799
    | exact resolve eq91799 eq81547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91799
  have eq91812 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91806 eq28
    | exact resolve eq28 eq91806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91904 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91806 eq81984
    | exact resolve eq81984 eq91806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81984 eq91806
  have eq95910 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91904 eq81931
    | exact resolve eq81931 eq91904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81931 eq91904
  have eq95923 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq95910
  have eq95935 : x = (M.op x y) := by
    first
    | (have r₁ := eq95923
       have r₂ := eq91812
       grind)
    | exact resolve eq95923 eq91812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91812 eq95923
  have eq96937 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq95935 eq21
    | exact resolve eq21 eq95935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq97180 : x = (k x x) := by
    first
    | exact superpose eq95935 eq81871
    | exact resolve eq81871 eq95935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81871 eq95935
  have eq97370 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96937
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96937
    | exact resolve eq96937 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96937
  have eq97975 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3754 x
       have i₂ := eq97180
       grind)
    | exact superpose eq97180 eq3754
    | (have j0 := eq3754 x
       grind)
    | exact resolve eq3754 eq97180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754 eq97180
  have eq97979 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq97975
  have eq97996 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq97979
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq97979
    | exact resolve eq97979 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq97979
  have eq98013 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81547 eq97996
    | exact resolve eq97996 eq81547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81547 eq97996
  have eq98029 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97370 eq98013
    | exact resolve eq98013 eq97370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97370 eq98013
  have eq98044 : False := by grind
  exact eq98044

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq181 X0 X0
       grind)
    | exact superpose eq181 eq178
    | exact resolve eq178 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq195
    | exact resolve eq195 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq195
  have eq658 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X2)) (M.op X1 X1)) = X1 ∨ (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 (M.op X1 X2)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (M.op X1 X2)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq40 (M.op x x)
       have i₂ := eq578 x
       grind)
    | exact superpose eq578 eq40
    | exact resolve eq40 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1096 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x x)) (M.op x x)) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq16 y x y
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq16
    | exact resolve eq16 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq1097 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq1096 x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq1096
    | exact resolve eq1096 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1120 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq673 eq16
    | exact resolve eq16 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq1121 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1120 x
       have i₂ := eq16 sF2 x sF2
       grind)
    | exact superpose eq16 eq1120
    | exact resolve eq1120 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1097
       grind)
    | exact superpose eq1097 eq41
    | exact resolve eq41 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1097
  have eq1127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1126
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1126
    | exact resolve eq1126 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq1127
    | exact resolve eq1127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1129 eq1121
    | exact resolve eq1121 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq1129
  have eq1144 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1137
       have r₂ := eq27
       grind)
    | exact resolve eq1137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1149 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1144 eq32
    | exact resolve eq32 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1144
  have eq1183 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1149
    | exact resolve eq1149 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1184 : x = y := by grind
  clear eq1183
  have eq1188 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1184
       grind)
    | exact superpose eq1184 eq18
    | exact resolve eq18 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1189 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1184
       grind)
    | exact superpose eq1184 eq24
    | exact resolve eq24 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1184
  have eq1202 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1189
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1189
    | exact resolve eq1189 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1189
  have eq1203 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1202 eq26
    | exact resolve eq26 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1202
  have eq1242 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq697
       have i₂ := eq1188
       grind)
    | exact superpose eq1188 eq697
    | exact resolve eq697 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1252 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq181 x X0
       have i₂ := eq1188
       grind)
    | exact superpose eq1188 eq181
    | exact resolve eq181 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq1188
       grind)
    | exact superpose eq1188 eq181
    | exact resolve eq181 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq1242
    | exact resolve eq1242 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1278 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1203 eq578
    | exact resolve eq578 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1281 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1203 eq181
    | exact resolve eq181 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1358 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq1278 eq142
    | exact resolve eq142 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1278
  have eq1433 : ∀ X0 : G, x = (M.op (k X0 x) (M.op x y)) ∨ (M.op X0 X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1252 X0
       have i₂ := eq28 X0 x
       grind)
    | exact superpose eq28 eq1252
    | (have j1 := eq28 X0 x
       grind)
    | exact resolve eq1252 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1448 : ∀ X0 : G, x = (M.op (k X0 x) (M.op x y)) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1433 X0
       have i₂ := eq1188
       grind)
    | exact superpose eq1188 eq1433
    | (have j0 := eq1433 X0
       grind)
    | exact resolve eq1433 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188 eq1433
  have eq1825 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (σ x)) (σ x)) ∨ (M.op X0 X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1281 eq658
    | exact resolve eq658 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq1850 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (σ x)) (σ x)) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1203 eq1825
    | (have j0 := eq1825 X0
       grind)
    | exact resolve eq1825 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq2703 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq1358 eq1448
    | (have j0 := eq1448 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq1448 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq2971 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1263 eq1850
    | (have j0 := eq1850 (σ (M.op x y))
       grind)
    | exact resolve eq1850 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq3006 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2971 eq28
    | (have j0 := eq28 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq2971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq3014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1263 eq3006
    | exact resolve eq3006 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq3006
  have eq3016 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3014
       have r₂ := eq27
       grind)
    | exact resolve eq3014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq3018 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1203 eq3016
    | exact resolve eq3016 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq3016
  have eq3019 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3018
  have eq3043 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3019 eq181
    | exact resolve eq181 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019
  have eq3047 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1281 eq3043
    | exact resolve eq3043 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq3043
  have eq3051 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq3047 eq29
    | exact resolve eq29 eq3047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3047
  have eq3108 : x = (M.op x y) := by
    first
    | exact superpose eq3051 eq30
    | exact resolve eq30 eq3051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3051
  have eq3149 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq1358
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq1358
    | exact resolve eq1358 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq5141 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq2703 eq181
    | exact resolve eq181 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq2703
  have eq5147 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq1258 eq5141
    | exact resolve eq5141 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5141
  have eq5169 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq5147
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq5147
    | exact resolve eq5147 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5147
  have eq5177 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5169
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq5169
    | exact resolve eq5169 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169
  have eq5192 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5177 eq28
    | (have j0 := eq28 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq5177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq5199 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3149 eq5192
    | exact resolve eq5192 eq3149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149 eq5192
  have eq5200 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq5199
  have eq5204 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1258 eq5200
    | exact resolve eq5200 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq5200
  have eq5206 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5204
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq5204
    | exact resolve eq5204 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108 eq5204
  have eq5215 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5206 eq178
    | exact resolve eq178 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq5206
  have eq5246 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5177 eq5215
    | exact resolve eq5215 eq5177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177 eq5215
  have eq5247 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq5246
  have eq5266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5247 eq14
    | exact resolve eq14 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247
  have eq5278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5266
    | exact resolve eq5266 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5266
  have eq5282 : False := by grind
  exact eq5282

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq33
    | exact resolve eq33 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X2 (M.op X0 X1) X1
       have i₂ := eq24 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq24 eq21
    | exact resolve eq21 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X4 X0 X2
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq65 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq65
    | exact resolve eq65 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq114 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq134 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq16
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq24
    | (have j1 := eq43 X0 X0
       grind)
    | exact resolve eq24 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq154 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq244 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X1 X0 X2
       grind)
    | exact superpose eq21 eq32
    | exact resolve eq32 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq339 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq244 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq244
    | exact resolve eq244 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq394 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq339 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq339
    | exact resolve eq339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq339 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq339
    | exact resolve eq339 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X3 X1)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq339 (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X3 X0 X2
       grind)
    | exact superpose eq21 eq339
    | exact resolve eq339 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 X0 X1 X2
       have i₂ := eq395 (M.op X0 X2) X1
       grind)
    | exact superpose eq395 eq394
    | exact resolve eq394 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq626 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 X0)
       have i₂ := eq395 X0 X1
       grind)
    | exact superpose eq395 eq22
    | exact resolve eq22 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 X1
       have i₂ := eq417 X1 X0 X0
       grind)
    | exact superpose eq417 eq626
    | exact resolve eq626 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq626
  have eq777 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X1 X0 X1 X0 X2
       have i₂ := eq635 X1 X0
       grind)
    | exact superpose eq635 eq99
    | exact resolve eq99 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq838 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq777 X0 X1 X2
       have i₂ := eq395 X0 X2
       grind)
    | exact superpose eq395 eq777
    | exact resolve eq777 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1160 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X2 X1 X1
       have i₂ := eq838 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq838 eq21
    | exact resolve eq21 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq838
  have eq1672 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq635 X2 X1
       have i₂ := eq1160 X1 X2 X0
       grind)
    | (have i₁ := eq635 (M.op X2 X0) X0
       have i₂ := eq1160 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1160 eq635
    | exact resolve eq635 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq2756 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq134
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq134 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq2757 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq2756
  have eq10515 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq154
    | exact resolve eq154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10531 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0
       have i₂ := eq154 X0 X1
       grind)
    | exact superpose eq154 eq114
    | (have j1 := eq154 X0 X1
       grind)
    | exact resolve eq114 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq10631 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10531 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10531
    | (have j0 := eq10531 X0 X1
       grind)
    | exact resolve eq10531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10531
  have eq10643 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10515 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq10515
    | (have j0 := eq10515 X0 X1
       grind)
    | exact resolve eq10515 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10515
  have eq10649 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10643 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10643
    | (have j0 := eq10643 X0 X1
       grind)
    | exact resolve eq10643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10643
  have eq10714 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq339 (k X0 X0) X0
       have i₂ := eq10649 X0 (k X0 X0)
       grind)
    | exact superpose eq10649 eq339
    | (have j1 := eq10649 X0 x
       grind)
    | exact resolve eq339 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10649
  have eq10888 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 (k X0 X0) (k X0 X0)
       have i₂ := eq10714 X0
       grind)
    | exact superpose eq10714 eq24
    | (have j1 := eq10714 X0
       grind)
    | exact resolve eq24 eq10714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10714
  have eq11233 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq10888 (σ X0)
       grind)
    | exact superpose eq10888 eq15
    | (have j1 := eq10888 (σ X0)
       grind)
    | exact resolve eq15 eq10888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10888
  have eq36783 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10631 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq10631
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq10631 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10631
  have eq36893 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq36783 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36783
  have eq38489 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) = (M.op (M.op X4 X3) (M.op X3 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X3 X1 X4
       have i₂ := eq396 X0 X1 X2 X3
       grind)
    | exact superpose eq396 eq96
    | exact resolve eq96 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq396
  have eq40907 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq2757
       grind)
    | exact superpose eq2757 eq24
    | exact resolve eq24 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq40998 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq40907
  have eq44450 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq339 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq36893 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq36893 eq339
    | (have j1 := eq36893 X0 x
       grind)
    | exact resolve eq339 eq36893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36893
  have eq51279 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X3 X2) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38489 X0 X1 (M.op X0 X1) X2 X3
       have i₂ := eq635 X1 X0
       grind)
    | exact superpose eq635 eq38489
    | exact resolve eq38489 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq38489
  have eq173847 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq11233
  have eq174138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq173847 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq173847
    | (have j0 := eq173847 X0
       grind)
    | exact resolve eq173847 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173847
  have eq174139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq174138 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174138
  have eq174219 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq174139 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174139
    | exact resolve eq174139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174321 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq174139 X0
       grind)
    | exact superpose eq174139 eq114
    | exact resolve eq114 eq174139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq174387 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq174139 X0
       grind)
    | exact superpose eq174139 eq34
    | exact resolve eq34 eq174139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq174742 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq174387 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq174387
    | exact resolve eq174387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174387
  have eq174766 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq174321 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq174321
    | exact resolve eq174321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174321
  have eq174805 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq174219 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq174219
    | exact resolve eq174219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq174219
  have eq174893 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq174805 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174805
    | exact resolve eq174805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174805
  have eq178531 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq174139 (k X0 (k X0 X0))
       have i₂ := eq174742 X0
       grind)
    | exact superpose eq174742 eq174139
    | exact resolve eq174139 eq174742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174742
  have eq178539 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq178531 X0
       have i₂ := eq174893 (k X0 (k X0 X0))
       grind)
    | exact superpose eq174893 eq178531
    | exact resolve eq178531 eq174893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178531
  have eq178684 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178539 X0
       have i₂ := eq174766 X0
       grind)
    | exact superpose eq174766 eq178539
    | exact resolve eq178539 eq174766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174766 eq178539
  have eq184068 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq178684 X0
       grind)
    | exact superpose eq178684 eq24
    | exact resolve eq24 eq178684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq184159 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq339 (σ X0) (σ X0)
       have i₂ := eq178684 X0
       grind)
    | exact superpose eq178684 eq339
    | exact resolve eq339 eq178684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184215 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1672 X0 (σ X0) (σ X0)
       have i₂ := eq178684 X0
       grind)
    | exact superpose eq178684 eq1672
    | exact resolve eq1672 eq178684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq198206 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X2)) = (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184068 (M.op X1 X2) X3
       have i₂ := eq51279 X1 X2 X1 X0
       grind)
    | (have i₁ := eq184068 (M.op X1 X1) X1
       have i₂ := eq51279 X0 X1 X1 X1
       grind)
    | exact superpose eq51279 eq184068
    | exact resolve eq184068 eq51279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184068
  have eq324916 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184215 (M.op X2 X1) X1
       have i₂ := eq51279 X2 X1 X2 X3
       grind)
    | (have i₁ := eq184215 (M.op X1 X1) X1
       have i₂ := eq51279 X0 X1 X1 X1
       grind)
    | exact superpose eq51279 eq184215
    | exact resolve eq184215 eq51279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51279 eq184215
  have eq325561 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324916 X0 X1 X2 x
       have i₂ := eq198206 X0 X1 X2 x
       grind)
    | exact superpose eq198206 eq324916
    | exact resolve eq324916 eq198206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198206 eq324916
  have eq325884 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (k (M.op X1 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq325561 X0 X1 X2
       have i₂ := eq174139 (M.op X1 X2)
       grind)
    | exact superpose eq174139 eq325561
    | exact resolve eq325561 eq174139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325561
  have eq326067 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X2) (M.op X1 X2))) = (σ (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq325884 X0 X1 X2
       have i₂ := eq174893 (M.op X1 X2)
       grind)
    | exact superpose eq174893 eq325884
    | exact resolve eq325884 eq174893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325884
  have eq326184 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq326067 X0 X1 X2
       have i₂ := eq395 X2 X1
       grind)
    | exact superpose eq395 eq326067
    | exact resolve eq326067 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq326067
  have eq1477237 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq44450 y
       have i₂ := eq40998
       grind)
    | exact superpose eq40998 eq44450
    | exact resolve eq44450 eq40998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40998 eq44450
  have eq1477644 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1477237
  have eq1478039 : (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1477644
       have i₂ := eq174139 x
       grind)
    | exact superpose eq174139 eq1477644
    | exact resolve eq1477644 eq174139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477644
  have eq1478532 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1478039
       have i₂ := eq174893 x
       grind)
    | exact superpose eq174893 eq1478039
    | exact resolve eq1478039 eq174893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478039
  have eq1479018 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq1478532
       have i₂ := eq174139 y
       grind)
    | exact superpose eq174139 eq1478532
    | exact resolve eq1478532 eq174139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478532
  have eq1479503 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1479018
       have i₂ := eq174893 y
       grind)
    | exact superpose eq174893 eq1479018
    | exact resolve eq1479018 eq174893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479018
  have eq1479781 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1479503
       grind)
    | exact superpose eq1479503 eq16
    | exact resolve eq16 eq1479503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479503
  have eq1479784 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1479781
       have r₂ := eq178684 x
       grind)
    | exact resolve eq1479781 eq178684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479781
  have eq1480307 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq178684 (M.op x x)
       have i₂ := eq1479784
       grind)
    | exact superpose eq1479784 eq178684
    | exact resolve eq178684 eq1479784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178684 eq1479784
  have eq1480375 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1480307
       have i₂ := eq326184 x x x
       grind)
    | exact superpose eq326184 eq1480307
    | exact resolve eq1480307 eq326184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326184 eq1480307
  have eq1480866 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1480375
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq1480375
    | exact resolve eq1480375 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1480375
  have eq1481296 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1480866
       have i₂ := eq174139 y
       grind)
    | exact superpose eq174139 eq1480866
    | exact resolve eq1480866 eq174139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174139 eq1480866
  have eq1481538 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1481296
       have i₂ := eq174893 y
       grind)
    | exact superpose eq174893 eq1481296
    | exact resolve eq1481296 eq174893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174893 eq1481296
  have eq1481539 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1481538
  have eq1486450 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184159 y
       have i₂ := eq1481539
       grind)
    | exact superpose eq1481539 eq184159
    | exact resolve eq184159 eq1481539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184159
  have eq1486476 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1481539
       grind)
    | exact superpose eq1481539 eq10
    | exact resolve eq10 eq1481539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481539
  have eq1487424 : x = (M.op y y) := by
    first
    | (have i₁ := eq1486476
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1486476
    | exact resolve eq1486476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486476
  have eq1489207 : x = (M.op x y) := by
    first
    | (have i₁ := eq339 y y
       have i₂ := eq1487424
       grind)
    | exact superpose eq1487424 eq339
    | exact resolve eq339 eq1487424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq1487424
  have eq1522180 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1486450
       grind)
    | exact superpose eq1486450 eq16
    | exact resolve eq16 eq1486450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486450
  have eq1522821 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1522180
       have i₂ := eq1489207
       grind)
    | exact superpose eq1489207 eq1522180
    | exact resolve eq1522180 eq1489207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489207 eq1522180
  have eq1522822 : False := by grind
  exact eq1522822

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
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
  clear eq36
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq72
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq325 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq65 (τ X0)
       grind)
    | exact superpose eq65 eq39
    | exact resolve eq39 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq344 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq325
    | exact resolve eq325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq406 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq53
  have eq550 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq54
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq54 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq562 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq3258 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq3284 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3258 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3258
    | (have j0 := eq3258 y x
       grind)
    | exact resolve eq3258 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3286 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3258
    | (have j0 := eq3258 (σ y) (σ x)
       grind)
    | exact resolve eq3258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3433 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq423 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq423
    | exact resolve eq423 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq3481 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3433 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq3433
    | exact resolve eq3433 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq3433
  have eq3705 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq562 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq562
    | (have j0 := eq562 (τ X0)
       grind)
    | exact resolve eq562 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq3725 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3705 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3705
    | (have j0 := eq3705 X0
       grind)
    | exact resolve eq3705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq3737 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3725 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3725
    | (have j0 := eq3725 X0
       grind)
    | exact resolve eq3725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq3756 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq414 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq414
    | exact resolve eq414 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq6734 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq406
    | exact resolve eq406 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq11992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11992
    | exact resolve eq11992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992
  have eq12004 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11993
       have r₂ := eq28
       grind)
    | exact resolve eq11993 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11993
  have eq12006 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12004
    | exact resolve eq12004 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12004
  have eq12032 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12006 eq3258
    | exact resolve eq3258 eq12006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12006
  have eq12033 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12032
    | exact resolve eq12032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12032
  have eq12034 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12033
  have eq12063 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3258 y y
       have i₂ := eq12034
       grind)
    | exact superpose eq12034 eq3258
    | exact resolve eq3258 eq12034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034
  have eq12064 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12063
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12063
    | exact resolve eq12063 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12063
  have eq12065 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12064
  have eq12079 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12065 eq3286
    | exact resolve eq3286 eq12065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq12087 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12079
    | exact resolve eq12079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12079
  have eq12215 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12087 eq65
    | exact resolve eq65 eq12087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12406 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12065 eq12215
    | exact resolve eq12215 eq12065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12065 eq12215
  have eq12414 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12406
  have eq12884 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12414 eq83
    | exact resolve eq83 eq12414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq12414
  have eq12897 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12884
  have eq14618 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3258 y y
       have i₂ := eq12897
       grind)
    | exact superpose eq12897 eq3258
    | exact resolve eq3258 eq12897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12897
  have eq14619 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14618
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14618
    | exact resolve eq14618 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14618
  have eq14620 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14619
  have eq14627 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14620 eq30
    | exact resolve eq30 eq14620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14629 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14620 eq41
    | exact resolve eq41 eq14620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq14700 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14620 eq12087
    | exact resolve eq12087 eq14620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12087
  have eq14741 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq14700
  have eq14799 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42 eq14629
    | exact resolve eq14629 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq14801 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq14627
    | exact resolve eq14627 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14627
  have eq14866 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14801 eq3481
    | exact resolve eq3481 eq14801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481
  have eq14869 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19711 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3756 x
       have i₂ := eq14866
       grind)
    | exact superpose eq14866 eq3756
    | exact resolve eq3756 eq14866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756 eq14866
  have eq19777 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19711
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq19711
    | exact resolve eq19711 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19711
  have eq21043 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19777 eq14
    | exact resolve eq14 eq19777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19777
  have eq34484 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14799 eq35
    | exact resolve eq35 eq14799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14799
  have eq34642 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq34484
    | (have j0 := eq34484 X0
       grind)
    | exact resolve eq34484 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34484
  have eq34680 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34642 X0
       have i₂ := eq35 X0 y
       grind)
    | exact superpose eq35 eq34642
    | exact resolve eq34642 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq34642
  have eq34700 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34680 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34680
    | (have j0 := eq34680 X0
       grind)
    | exact resolve eq34680 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34680
  have eq35022 : (σ y) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34700 eq344
    | exact resolve eq344 eq34700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq34700
  have eq35101 : (σ y) = (σ (k (M.op (τ (σ y)) (τ (σ y))) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq35022
    | exact resolve eq35022 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq35022
  have eq35156 : (σ y) = (σ (k (M.op y y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq35101
    | exact resolve eq35101 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35101
  have eq35654 : (τ (σ y)) = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35156 eq16
    | exact resolve eq16 eq35156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35156
  have eq35731 : y = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq35654
    | exact resolve eq35654 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35654
  have eq126476 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21043 eq6734
    | exact resolve eq6734 eq21043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734 eq21043
  have eq126825 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14801 eq126476
    | exact resolve eq126476 eq14801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14801 eq126476
  have eq126887 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126825
       have r₂ := eq14869
       grind)
    | exact resolve eq126825 eq14869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14869 eq126825
  have eq126888 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126887
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq126887
    | exact resolve eq126887 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126887
  have eq126899 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35731
       have i₂ := eq126888
       grind)
    | exact superpose eq126888 eq35731
    | exact resolve eq35731 eq126888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35731 eq126888
  have eq126941 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq126899
  have eq127268 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126941 eq557
    | (have j0 := eq557 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq557 eq126941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq126941
  have eq127272 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq127268
  have eq127293 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq127272
    | exact resolve eq127272 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127272
  have eq127322 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127293
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq127293
    | exact resolve eq127293 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127293
  have eq127334 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127322
       have r₂ := eq14620
       grind)
    | exact resolve eq127322 eq14620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14620 eq127322
  have eq127343 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq127334
    | exact resolve eq127334 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127334
  have eq130569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127343 eq14741
    | exact resolve eq14741 eq127343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14741 eq127343
  have eq130721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq130569
  have eq130733 : x = (M.op x y) := by
    first
    | (have r₁ := eq130721
       have r₂ := eq28
       grind)
    | exact resolve eq130721 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130721
  have eq131402 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq130733 eq21
    | exact resolve eq21 eq130733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq131542 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq130733 eq3284
    | exact resolve eq3284 eq130733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq131556 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq131542
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq131542
    | exact resolve eq131542 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq131542
  have eq131684 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq131402
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq131402
    | exact resolve eq131402 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131402
  have eq131685 : x = (M.op y y) := by
    first
    | exact superpose eq130733 eq131556
    | exact resolve eq131556 eq130733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130733 eq131556
  have eq131686 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq131684 eq27
    | exact resolve eq27 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq132075 : y = (k x y) := by
    first
    | (have i₁ := eq65 y
       have i₂ := eq131685
       grind)
    | exact superpose eq131685 eq65
    | exact resolve eq65 eq131685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132087 : y = (M.op x x) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq131685
       grind)
    | exact superpose eq131685 eq56
    | exact resolve eq56 eq131685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq131685
  have eq132262 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq132075
       grind)
    | exact superpose eq132075 eq45
    | exact resolve eq45 eq132075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq132075
  have eq132313 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq131684 eq132262
    | exact resolve eq132262 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132262
  have eq132332 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq132313
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq132313
    | exact resolve eq132313 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132313
  have eq132499 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq132087
       grind)
    | exact superpose eq132087 eq78
    | exact resolve eq78 eq132087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq132087
  have eq132559 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq131684 eq132499
    | exact resolve eq132499 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132499
  have eq132566 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq132559
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq132559
    | exact resolve eq132559 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132559
  have eq132691 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq132332 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq132332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132332
  have eq132699 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq131686 eq132691
    | exact resolve eq132691 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132691
  have eq132712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq131686 eq132699
    | exact resolve eq132699 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132699
  have eq132725 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq132712
       have r₂ := eq28
       grind)
    | exact resolve eq132712 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132712
  have eq140967 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq132566 eq3737
    | (have j0 := eq3737 (σ (M.op x y))
       grind)
    | exact resolve eq3737 eq132566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq140985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq131686 eq140967
    | exact resolve eq140967 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140967
  have eq140996 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq140985
       have r₂ := eq28
       grind)
    | exact resolve eq140985 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140985
  have eq141294 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132725 eq3258
    | exact resolve eq3258 eq132725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3258 eq132725
  have eq141304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131686 eq141294
    | exact resolve eq141294 eq131686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131686 eq141294
  have eq141311 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq141304
       have r₂ := eq28
       grind)
    | exact resolve eq141304 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141304
  have eq141317 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq141311 eq28
    | exact resolve eq28 eq141311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq141311
  have eq141938 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq140996 eq65
    | exact resolve eq65 eq140996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq140996
  have eq143913 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq141938 eq132566
    | exact resolve eq132566 eq141938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132566 eq141938
  have eq143956 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq143913
  have eq143967 : x = y := by
    first
    | (have r₁ := eq143956
       have r₂ := eq141317
       grind)
    | exact resolve eq143956 eq141317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143956
  have eq143998 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq143967
       grind)
    | exact superpose eq143967 eq25
    | exact resolve eq25 eq143967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq143967
  have eq144365 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq143998
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq143998
    | exact resolve eq143998 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq143998
  have eq144503 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq131684 eq144365
    | exact resolve eq144365 eq131684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131684 eq144365
  have eq144584 : False := by grind
  exact eq144584
