import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1256`: `x = x ◇ (((y ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pxy_pyx_Equation1256 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1256 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1256.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq27 X0 x x X3
       have i₂ := eq9 (M.op X0 X0) x x
       grind)
    | exact superpose eq9 eq27
    | exact resolve eq27 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq85 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq28
    | exact resolve eq28 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53 x y
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 x y
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6739 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq353
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq353
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq353
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq353
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq353 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq6748 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq6739
  have eq122335 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6748
       grind)
    | exact superpose eq6748 eq10
    | exact resolve eq10 eq6748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6748
  have eq122336 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq122335
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq122335
    | exact resolve eq122335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122335
  have eq122337 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq122336
  have eq122343 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq28 x X0
       have i₂ := eq122337
       grind)
    | exact superpose eq122337 eq28
    | exact resolve eq28 eq122337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq122346 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq85 x X0
       have i₂ := eq122337
       grind)
    | exact superpose eq122337 eq85
    | exact resolve eq85 eq122337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq122337
  have eq123115 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq122346 (σ x)
       grind)
    | exact superpose eq122346 eq16
    | exact resolve eq16 eq122346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122346
  have eq124279 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq123115
       have i₂ := eq122343 x
       grind)
    | exact superpose eq122343 eq123115
    | exact resolve eq123115 eq122343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122343 eq123115
  have eq124280 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq124279
  have eq124281 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq124280
  have eq124312 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq124281
       grind)
    | exact superpose eq124281 eq10
    | exact resolve eq10 eq124281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124281
  have eq124366 : x = y ∨ x = y := by
    first
    | (have i₁ := eq124312
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq124312
    | exact resolve eq124312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124312
  have eq124367 : x = y := by grind
  clear eq124366
  have eq124390 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124367
       grind)
    | exact superpose eq124367 eq16
    | exact resolve eq16 eq124367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124367
  have eq124395 : False := by grind
  exact eq124395

/-- `Equation1264`: `x = x ◇ (((y ◇ z) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation1264 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1264 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1264.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
    intro X0 X1 X2
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq9 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq26 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq75 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq27
    | exact resolve eq27 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq288 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq279
    | (have j0 := eq279 X0 X1
       grind)
    | exact resolve eq279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq2205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2290 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2205 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2205
    | (have j0 := eq2205 (M.op X1 X1) X1
       grind)
    | exact resolve eq2205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq4267 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 y x
       grind)
    | exact superpose eq288 eq16
    | (have j1 := eq288 y x
       grind)
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq72209 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq4267
       have i₂ := eq2290 x y
       grind)
    | exact superpose eq2290 eq4267
    | (have j1 := eq2290 (M.op y y) y
       grind)
    | (have r₁ := eq4267
       have r₂ := eq2290 x y
       grind)
    | (have r₁ := eq4267
       have r₂ := eq2290 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4267
       have r₂ := eq2290 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4267 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290 eq4267
  have eq72210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq72209
  have eq72211 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq72210
  have eq72217 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27 y X0
       have i₂ := eq72211
       grind)
    | exact superpose eq72211 eq27
    | exact resolve eq27 eq72211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq72223 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq75 y X0
       have i₂ := eq72211
       grind)
    | exact superpose eq72211 eq75
    | exact resolve eq75 eq72211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq72211
  have eq74421 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq72223 (σ x)
       grind)
    | exact superpose eq72223 eq16
    | exact resolve eq16 eq72223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72223
  have eq77845 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq74421
       have i₂ := eq72217 x
       grind)
    | exact superpose eq72217 eq74421
    | exact resolve eq74421 eq72217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72217 eq74421
  have eq77846 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq77845
  have eq77847 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq77846
  have eq78156 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq77847
       grind)
    | exact superpose eq77847 eq10
    | exact resolve eq10 eq77847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77847
  have eq78228 : x = y ∨ x = y := by
    first
    | (have i₁ := eq78156
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78156
    | exact resolve eq78156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78156
  have eq78229 : x = y := by grind
  clear eq78228
  have eq78542 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78229
       grind)
    | exact superpose eq78229 eq16
    | exact resolve eq16 eq78229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78229
  have eq78543 : False := by grind
  exact eq78543

/-- `Equation1267`: `x = x ◇ (((y ◇ z) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation1267 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1267 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1267.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) = X0 := by
    intro X0 X1 X2
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op (M.op X1 X2) X2) X1)
       have i₂ := eq9 (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq75 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq27
    | exact resolve eq27 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq288 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq279
    | (have j0 := eq279 X0 X1
       grind)
    | exact resolve eq279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq2205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2290 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2205 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2205
    | (have j0 := eq2205 (M.op X1 X1) X1
       grind)
    | exact resolve eq2205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq4267 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 y x
       grind)
    | exact superpose eq288 eq16
    | (have j1 := eq288 y x
       grind)
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq65055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq4267
       have i₂ := eq2290 x y
       grind)
    | exact superpose eq2290 eq4267
    | (have j1 := eq2290 (M.op y y) y
       grind)
    | (have r₁ := eq4267
       have r₂ := eq2290 x y
       grind)
    | (have r₁ := eq4267
       have r₂ := eq2290 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4267
       have r₂ := eq2290 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4267 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290 eq4267
  have eq65056 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65055
  have eq65057 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65056
  have eq65063 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27 y X0
       have i₂ := eq65057
       grind)
    | exact superpose eq65057 eq27
    | exact resolve eq27 eq65057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq65069 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq75 y X0
       have i₂ := eq65057
       grind)
    | exact superpose eq65057 eq75
    | exact resolve eq75 eq65057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq65057
  have eq67129 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq65069 (σ x)
       grind)
    | exact superpose eq65069 eq16
    | exact resolve eq16 eq65069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65069
  have eq70357 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67129
       have i₂ := eq65063 x
       grind)
    | exact superpose eq65063 eq67129
    | exact resolve eq67129 eq65063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65063 eq67129
  have eq70358 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq70357
  have eq70359 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq70358
  have eq70654 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq70359
       grind)
    | exact superpose eq70359 eq10
    | exact resolve eq10 eq70359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70359
  have eq70726 : x = y ∨ x = y := by
    first
    | (have i₁ := eq70654
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq70654
    | exact resolve eq70654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70654
  have eq70727 : x = y := by grind
  clear eq70726
  have eq71023 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70727
       grind)
    | exact superpose eq70727 eq16
    | exact resolve eq16 eq70727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70727
  have eq71024 : False := by grind
  exact eq71024

/-- `Equation1315`: `x = y ◇ (((y ◇ x) ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1315 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1315 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1315.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq79 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq84 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq329 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq360 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq329
    | (have j0 := eq329 X0 X1
       grind)
    | exact resolve eq329 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq720 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq79
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq79
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq79
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq79 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq721 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq720
  have eq5053 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq721
       grind)
    | exact superpose eq721 eq16
    | exact resolve eq16 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5057 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq721
       grind)
    | exact superpose eq721 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq721
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq721
       grind)
    | exact resolve eq13 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq5072 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq5057
  have eq5073 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq5072
  have eq5083 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5073
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5073
    | exact resolve eq5073 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5073
  have eq8220 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq360 x y
       have i₂ := eq5083
       grind)
    | exact superpose eq5083 eq360
    | (have j0 := eq360 x y
       grind)
    | exact resolve eq360 eq5083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq5083
  have eq8272 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8220
  have eq8303 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8272
       have r₂ := eq5053
       grind)
    | exact resolve eq8272 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5053 eq8272
  have eq8489 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8303
       grind)
    | exact superpose eq8303 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8303
       grind)
    | exact resolve eq13 eq8303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8504 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq8489
  have eq8505 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8504
  have eq8711 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq84 x y
       have i₂ := eq8505
       grind)
    | exact superpose eq8505 eq84
    | (have j0 := eq84 x y
       grind)
    | exact resolve eq84 eq8505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq8505
  have eq8723 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8711
  have eq8724 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8723
  have eq8886 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq8724
       grind)
    | exact superpose eq8724 eq16
    | exact resolve eq16 eq8724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8724
  have eq9118 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8886
       have i₂ := eq8303
       grind)
    | exact superpose eq8303 eq8886
    | exact resolve eq8886 eq8303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8303 eq8886
  have eq9119 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9118
  have eq9120 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq9119
  have eq9325 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9120
       grind)
    | exact superpose eq9120 eq10
    | exact resolve eq10 eq9120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9120
  have eq9406 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9325
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9325
    | exact resolve eq9325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325
  have eq9407 : x = y := by grind
  clear eq9406
  have eq9469 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9407
       grind)
    | exact superpose eq9407 eq16
    | exact resolve eq16 eq9407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9407
  have eq9470 : False := by grind
  exact eq9470

/-- `Equation1353`: `x = y ◇ (((z ◇ x) ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1353 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1353 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1353.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq129 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1103 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1103
    | (have j0 := eq1103 X0 X1
       grind)
    | exact resolve eq1103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq129
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq129
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq129
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq129 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq1999 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1998
  have eq27287 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq16
    | exact resolve eq16 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27306 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1999
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1999
       grind)
    | exact resolve eq13 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq27403 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq27306
  have eq27404 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq27403
  have eq27416 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq27404
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq27404
    | exact resolve eq27404 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27404
  have eq33437 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1142 x y
       have i₂ := eq27416
       grind)
    | exact superpose eq27416 eq1142
    | (have j0 := eq1142 x y
       grind)
    | exact resolve eq1142 eq27416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq33438 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq27416
       grind)
    | exact superpose eq27416 eq10
    | exact resolve eq10 eq27416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27416
  have eq33510 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33437
  have eq33542 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq33438
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33438
    | exact resolve eq33438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33438
  have eq33543 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq33510
       have r₂ := eq27287
       grind)
    | exact resolve eq33510 eq27287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27287 eq33510
  have eq33546 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq33542
       have r₂ := eq13 x y
       grind)
    | exact resolve eq33542 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33542
  have eq34492 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq139 x y
       have i₂ := eq33546
       grind)
    | exact superpose eq33546 eq139
    | (have j0 := eq139 x y
       grind)
    | exact resolve eq139 eq33546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq33546
  have eq34504 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34492
  have eq34505 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34504
  have eq35305 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq34505
       grind)
    | exact superpose eq34505 eq16
    | exact resolve eq16 eq34505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34505
  have eq35624 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35305
       have i₂ := eq33543
       grind)
    | exact superpose eq33543 eq35305
    | exact resolve eq35305 eq33543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33543 eq35305
  have eq35625 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35624
  have eq35626 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq35625
  have eq35863 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq35626
       grind)
    | exact superpose eq35626 eq10
    | exact resolve eq10 eq35626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35626
  have eq35959 : x = y ∨ x = y := by
    first
    | (have i₁ := eq35863
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35863
    | exact resolve eq35863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35863
  have eq35960 : x = y := by grind
  clear eq35959
  have eq36192 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35960
       grind)
    | exact superpose eq35960 eq16
    | exact resolve eq16 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35960
  have eq36193 : False := by grind
  exact eq36193

/-- `Equation1353`: `x = y ◇ (((z ◇ x) ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1353 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1353 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1353.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq129 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq139 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1103 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1142 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1103
    | (have j0 := eq1103 X0 X1
       grind)
    | exact resolve eq1103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq129
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq129
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq129
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq129 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq1998 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1997
  have eq27042 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1998
       grind)
    | exact superpose eq1998 eq16
    | exact resolve eq16 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27061 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1998
       grind)
    | exact superpose eq1998 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1998
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1998
       grind)
    | exact resolve eq13 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq27158 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq27061
  have eq27159 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq27158
  have eq27171 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq27159
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq27159
    | exact resolve eq27159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27159
  have eq33588 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1142 x y
       have i₂ := eq27171
       grind)
    | exact superpose eq27171 eq1142
    | (have j0 := eq1142 x y
       grind)
    | exact resolve eq1142 eq27171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq33589 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq27171
       grind)
    | exact superpose eq27171 eq10
    | exact resolve eq10 eq27171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27171
  have eq33661 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33588
  have eq33693 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq33589
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33589
    | exact resolve eq33589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33589
  have eq33694 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq33661
       have r₂ := eq27042
       grind)
    | exact resolve eq33661 eq27042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27042 eq33661
  have eq33697 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq33693
       have r₂ := eq13 y x
       grind)
    | exact resolve eq33693 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33693
  have eq34665 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq139 x y
       have i₂ := eq33697
       grind)
    | exact superpose eq33697 eq139
    | (have j0 := eq139 x y
       grind)
    | exact resolve eq139 eq33697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq33697
  have eq34677 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34665
  have eq34678 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34677
  have eq35474 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq34678
       grind)
    | exact superpose eq34678 eq16
    | exact resolve eq16 eq34678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34678
  have eq35846 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35474
       have i₂ := eq33694
       grind)
    | exact superpose eq33694 eq35474
    | exact resolve eq35474 eq33694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33694 eq35474
  have eq35847 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35846
  have eq35848 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq35847
  have eq36082 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq35848
       grind)
    | exact superpose eq35848 eq10
    | exact resolve eq10 eq35848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35848
  have eq36178 : x = y ∨ x = y := by
    first
    | (have i₁ := eq36082
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36082
    | exact resolve eq36082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36082
  have eq36179 : x = y := by grind
  clear eq36178
  have eq36377 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36179
       grind)
    | exact superpose eq36179 eq16
    | exact resolve eq16 eq36179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36179
  have eq36378 : False := by grind
  exact eq36378

/-- `Equation138`: `x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation138 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law138 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law138.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X1)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 (M.op X2 X1)) X0) X1 X2
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X4 : G, (M.op (M.op X1 X0) (M.op X0 X4)) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 X0) (M.op (M.op x x) X1)
       have i₂ := eq18 X1 x x X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq100 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq143 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 X0
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq47
    | (have j0 := eq47 X1 X0
       have j1 := eq47 X1 X0
       grind)
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) X2 (σ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq62
    | (have j1 := eq47 X0 X1
       grind)
    | exact resolve eq62 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ X0) X2)) = X2 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq9
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq9 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) X2) = (M.op (M.op X3 (σ X0)) X2) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0) X3
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq19
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq19 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq159 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq160 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq159 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq164 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq918 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq918 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq918
    | (have j0 := eq918 X0 X1
       grind)
    | exact resolve eq918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq1727 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq1774 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1727 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq1727
    | (have j0 := eq1727 X0 X1
       grind)
    | exact resolve eq1727 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1778 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1774 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq1774
    | (have j0 := eq1774 X0 X1
       grind)
    | exact resolve eq1774 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774
  have eq1961 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X2) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 X0 X1 (σ X2)
       have i₂ := eq47 X2 X0
       grind)
    | exact superpose eq47 eq151
    | (have j0 := eq151 X0 X2 X2
       have j1 := eq47 X2 X0
       grind)
    | exact resolve eq151 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq151
  have eq2591 : ∀ X0 X1 X2 X3 X4 : G, (σ X1) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (M.op (σ X0) X3) = (M.op (M.op X4 (σ X1)) X3) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (σ X0) X2 (σ X1)
       have i₂ := eq155 X1 X0 X3 X4
       grind)
    | exact superpose eq155 eq62
    | (have j1 := eq155 X1 X0 X3 X4
       grind)
    | exact resolve eq62 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq155
  have eq3208 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq162 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq162
    | exact resolve eq162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3235 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq162 X1 X0
       grind)
    | exact superpose eq162 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq162 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq162 X0 X1
       grind)
    | exact resolve eq13 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq3252 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235
  have eq3254 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3252 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq3252 X0 X1
       have r₂ := eq13 (σ X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq3252 X0 X1
       have r₂ := eq13 (σ (k X0 X1)) (σ X0)
       grind)
    | (have r₁ := eq3252 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq3252 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq3256 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3208 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq3208
    | (have j0 := eq3208 X0 X1
       grind)
    | exact resolve eq3208 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3208
  have eq3259 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3254 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3254
    | (have j0 := eq3254 X0 X1
       grind)
    | exact resolve eq3254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3260 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq3259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259
  have eq3262 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3256 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq3256
    | (have j0 := eq3256 X0 X1
       grind)
    | exact resolve eq3256 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3256
  have eq3266 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3262 X0 X1
       have j1 := eq13 (k (σ X1) X0) (M.op (σ X1) X0)
       grind)
    | (have r₁ := eq3262 (M.op (σ X1) X0) X1
       have r₂ := eq13 X0 (σ X1)
       grind)
    | (have r₁ := eq3262 X0 X1
       have r₂ := eq13 X0 (σ X1)
       grind)
    | exact resolve eq3262 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262
  have eq5939 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1778 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1778
    | exact resolve eq1778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq6041 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5939 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939
  have eq6190 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ X1)
       have i₂ := eq3266 (σ X0) X1
       grind)
    | exact superpose eq3266 eq40
    | (have j1 := eq3266 (σ X0) X1
       grind)
    | exact resolve eq40 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3266
  have eq6224 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6190 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6190
    | (have j0 := eq6190 X0 X1
       grind)
    | exact resolve eq6190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6190
  have eq6248 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6224 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6224
    | (have j0 := eq6224 X0 X1
       grind)
    | exact resolve eq6224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224
  have eq6262 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6248 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6248
    | (have j0 := eq6248 X0 X1
       grind)
    | exact resolve eq6248 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6248
  have eq33306 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X0))) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq150 (τ X0) (τ X1) X2
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq150
    | (have j0 := eq150 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq150 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq33505 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X0))) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33306 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq33306
    | (have j0 := eq33306 X0 X1 X2
       grind)
    | exact resolve eq33306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33306
  have eq33535 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 X0) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33505 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33505
    | (have j0 := eq33505 X0 X1 X2
       grind)
    | exact resolve eq33505 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33505
  have eq33551 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33535 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq33535
    | (have j0 := eq33535 X0 X1 X2
       grind)
    | exact resolve eq33535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33535
  have eq33565 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33551 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33551
    | (have j0 := eq33551 X0 X1 X2
       grind)
    | exact resolve eq33551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33551
  have eq33578 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33565 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33565
    | (have j0 := eq33565 X0 X1 X2
       grind)
    | exact resolve eq33565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33565
  have eq33591 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op (M.op X2 X0) (k X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33578 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq33578
    | (have j0 := eq33578 X0 X1 X2
       grind)
    | exact resolve eq33578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33578
  have eq33592 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33591 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33591
    | (have j0 := eq33591 X0 X1 X2
       grind)
    | exact resolve eq33591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33591
  have eq80210 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X0))) (σ (τ (k X0 X1)))) ∨ (M.op (σ (τ X0)) X3) = (M.op (M.op X4 (σ (τ X1))) X3) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2591 (τ X0) (τ X1) X2 X3 X4
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq2591
    | (have j0 := eq2591 (τ X0) (τ X1) X2 X3 X4
       grind)
    | exact resolve eq2591 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2591
  have eq81712 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X0))) (k X0 X1)) ∨ (M.op (σ (τ X0)) X3) = (M.op (M.op X4 (σ (τ X1))) X3) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq80210 X0 X1 X2 X3 X4
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq80210
    | (have j0 := eq80210 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq80210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80210
  have eq81775 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X1)) = (M.op (M.op X2 X0) (k X0 X1)) ∨ (M.op (σ (τ X0)) X3) = (M.op (M.op X4 (σ (τ X1))) X3) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81712 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81712
    | (have j0 := eq81712 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81712
  have eq81811 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (M.op (σ (τ X0)) X3) = (M.op (M.op X4 (σ (τ X1))) X3) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81775 X0 X1 X2 X3 X4
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq81775
    | (have j0 := eq81775 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81775
  have eq81836 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X3) = (M.op (σ (τ X0)) X3) ∨ (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81811 X0 X1 X2 X3 X4
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq81811
    | (have j0 := eq81811 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81811 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81811
  have eq81859 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X4 X1) X3) ∨ (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81836 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81836
    | (have j0 := eq81836 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81836
  have eq81882 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X3) = (M.op (M.op X4 X1) X3) ∨ (M.op (M.op X2 X0) (k X0 X1)) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81859 X0 X1 X2 X3 X4
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq81859
    | (have j0 := eq81859 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81859
  have eq81893 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (k X0 X1)) = X1 ∨ (M.op X0 X3) = (M.op (M.op X4 X1) X3) ∨ X0 = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq81882 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81882
    | (have j0 := eq81882 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq81882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81882
  have eq88250 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6262 y x
       grind)
    | exact superpose eq6262 eq16
    | (have j1 := eq6262 y x
       grind)
    | exact resolve eq16 eq6262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6262
  have eq89010 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq88250
       have i₂ := eq953 x y
       grind)
    | exact superpose eq953 eq88250
    | (have j1 := eq953 x y
       grind)
    | (have r₁ := eq88250
       have r₂ := eq953 x y
       grind)
    | (have r₁ := eq88250
       have r₂ := eq953 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq88250
       have r₂ := eq953 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq88250 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq88250
  have eq89011 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq89010
  have eq89014 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq6041 y x
       grind)
    | (have r₁ := eq89011
       have r₂ := eq6041 y x
       grind)
    | exact resolve eq89011 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041 eq89011
  have eq89645 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3260 y x
       have i₂ := eq89014
       grind)
    | exact superpose eq89014 eq3260
    | (have j0 := eq3260 y x
       grind)
    | exact resolve eq3260 eq89014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260
  have eq89652 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq33592 y x X0
       have i₂ := eq89014
       grind)
    | exact superpose eq89014 eq33592
    | (have j0 := eq33592 y x x
       grind)
    | exact resolve eq33592 eq89014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33592
  have eq89655 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq89652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89652
  have eq89663 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq89645
  have eq89664 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq89663
  have eq155198 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1961 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq155202 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq155198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155198
  have eq155203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq155202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155202
  have eq172240 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X0) (k X0 X2)) = X2 ∨ (M.op X2 (M.op X0 X1)) = X1 ∨ X0 = X2 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 X1 X2 x
       have i₂ := eq81893 X0 X2 X4 X1 x
       grind)
    | (have i₁ := eq9 x X1 X2
       have i₂ := eq81893 (M.op X2 X1) X1 X2 x X4
       grind)
    | exact superpose eq81893 eq9
    | (have j1 := eq81893 X0 X2 X4 x X4
       grind)
    | exact resolve eq9 eq81893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81893
  have eq172916 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X2) (k X2 X1)) = X1 ∨ (M.op X1 X0) = (M.op (M.op X3 X2) X0) ∨ X1 = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq172240 X2 (M.op (M.op X3 X2) X0) X1 X4
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq172240
    | (have j0 := eq172240 X2 X1 X1 X4
       grind)
    | exact resolve eq172240 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172240
  have eq285484 : ∀ X0 X1 X2 : G, (M.op X2 (k X1 X2)) ≠ X2 ∨ (M.op (M.op X0 X1) (k X1 X2)) = X2 ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq172916 X0 X2 X1 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172916
  have eq287494 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (M.op (M.op X0 y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq285484 X0 y x
       have i₂ := eq89014
       grind)
    | exact superpose eq89014 eq285484
    | (have j0 := eq285484 X0 x (M.op (M.op X0 y) y)
       grind)
    | exact resolve eq285484 eq89014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89014 eq285484
  have eq287495 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (M.op (M.op X0 y) y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq287494 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287494
  have eq287501 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq287495 X0
       have j1 := eq89655 X0
       grind)
    | (have r₁ := eq287495 X0
       have r₂ := eq89655 X0
       grind)
    | exact resolve eq287495 eq89655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287495
  have eq290056 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq89655 (M.op x y)
       have i₂ := eq287501 x
       grind)
    | exact superpose eq287501 eq89655
    | exact resolve eq89655 eq287501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89655 eq287501
  have eq290255 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq290056
  have eq428846 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq155203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155203
  have eq429226 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq428846 x y
       have i₂ := eq89664
       grind)
    | exact superpose eq89664 eq428846
    | (have j0 := eq428846 x y
       grind)
    | (have r₁ := eq428846 x y
       have r₂ := eq89664
       grind)
    | exact resolve eq428846 eq89664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89664 eq428846
  have eq429230 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq429226
  have eq429231 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq429230
  have eq429573 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq429231
       grind)
    | exact superpose eq429231 eq16
    | exact resolve eq16 eq429231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429231
  have eq429704 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq429573
       have i₂ := eq290255
       grind)
    | exact superpose eq290255 eq429573
    | exact resolve eq429573 eq290255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290255 eq429573
  have eq429711 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq429704
  have eq429712 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq429711
  have eq430031 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq429712
       grind)
    | exact superpose eq429712 eq10
    | exact resolve eq10 eq429712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429712
  have eq430214 : x = y ∨ x = y := by
    first
    | (have i₁ := eq430031
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq430031
    | exact resolve eq430031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430031
  have eq430215 : x = y := by grind
  clear eq430214
  have eq430228 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq430215
       grind)
    | exact superpose eq430215 eq16
    | exact resolve eq16 eq430215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430215
  have eq430229 : False := by grind
  exact eq430229

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq156 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1795 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1840 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1795 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1795
    | (have j0 := eq1795 X0 X1
       grind)
    | exact resolve eq1795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq3235 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq156
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq156
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq156
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq156
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq156 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq3236 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3235
  have eq17384 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3236
       grind)
    | exact superpose eq3236 eq16
    | exact resolve eq16 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17400 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3236
       grind)
    | exact superpose eq3236 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3236
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3236
       grind)
    | exact resolve eq13 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236
  have eq17456 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq17400
  have eq17457 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq17456
  have eq17459 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq17457
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17457
    | exact resolve eq17457 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17457
  have eq21018 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1840 x y
       have i₂ := eq17459
       grind)
    | exact superpose eq17459 eq1840
    | (have j0 := eq1840 x y
       grind)
    | exact resolve eq1840 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840 eq17459
  have eq21086 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq21018
  have eq21120 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq21086
       have r₂ := eq17384
       grind)
    | exact resolve eq21086 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17384 eq21086
  have eq21297 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq21120
       grind)
    | exact superpose eq21120 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21120
       grind)
    | exact resolve eq13 eq21120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21358 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq21297
  have eq21359 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq21358
  have eq21623 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq165 x y
       have i₂ := eq21359
       grind)
    | exact superpose eq21359 eq165
    | (have j0 := eq165 x y
       grind)
    | exact resolve eq165 eq21359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq21359
  have eq21649 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21623
  have eq21650 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21649
  have eq23576 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21650
       grind)
    | exact superpose eq21650 eq16
    | exact resolve eq16 eq21650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21650
  have eq23912 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23576
       have i₂ := eq21120
       grind)
    | exact superpose eq21120 eq23576
    | exact resolve eq23576 eq21120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21120 eq23576
  have eq23913 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23912
  have eq23914 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23913
  have eq24127 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23914
       grind)
    | exact superpose eq23914 eq10
    | exact resolve eq10 eq23914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23914
  have eq24223 : x = y ∨ x = y := by
    first
    | (have i₁ := eq24127
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24127
    | exact resolve eq24127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24127
  have eq24224 : x = y := by grind
  clear eq24223
  have eq24435 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24224
       grind)
    | exact superpose eq24224 eq16
    | exact resolve eq16 eq24224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24224
  have eq24436 : False := by grind
  exact eq24436
