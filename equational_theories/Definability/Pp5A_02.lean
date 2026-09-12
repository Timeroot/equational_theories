import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq389 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq16
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq2326 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq389
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq389
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq389
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq389
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq389 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq2327 : x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq2326
  have eq14603 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq78
  have eq14682 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14603 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq14603
    | (have j0 := eq14603 X0
       grind)
    | exact resolve eq14603 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq14603
  have eq14683 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14682
  have eq14694 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14683 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14683
    | exact resolve eq14683 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14683
  have eq14798 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq14694 X0
       have i₂ := eq27 (σ X0) X0
       grind)
    | exact superpose eq27 eq14694
    | exact resolve eq14694 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14694
  have eq14807 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14798 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14798
    | exact resolve eq14798 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14798
  have eq15275 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq14807 (σ X0)
       grind)
    | exact superpose eq14807 eq15
    | exact resolve eq15 eq14807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15275 X0
       have i₂ := eq14807 X0
       grind)
    | exact superpose eq14807 eq15275
    | exact resolve eq15275 eq14807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807 eq15275
  have eq15384 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq15464 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15384 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq15384
    | exact resolve eq15384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15384
  have eq15494 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq15464
  have eq47247 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2327
       grind)
    | exact superpose eq2327 eq16
    | exact resolve eq16 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq47248 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq47247
       have r₂ := eq15294 x
       grind)
    | exact resolve eq47247 eq15294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47247
  have eq47249 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq47248
       have i₂ := eq15294 x
       grind)
    | exact superpose eq15294 eq47248
    | exact resolve eq47248 eq15294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47248
  have eq47263 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq47249
       grind)
    | exact superpose eq47249 eq10
    | exact resolve eq10 eq47249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47249
  have eq47363 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq47263
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq47263
    | exact resolve eq47263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47263
  have eq47384 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47363
       grind)
    | exact superpose eq47363 eq16
    | exact resolve eq16 eq47363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47363
  have eq47385 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq47384
       have r₂ := eq15294 x
       grind)
    | exact resolve eq47384 eq15294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15294 eq47384
  have eq48175 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq47385
       grind)
    | exact superpose eq47385 eq10
    | exact resolve eq10 eq47385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47385
  have eq48281 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48175
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq48175
    | exact resolve eq48175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48175
  have eq48282 : y = (M.op x x) := by grind
  clear eq48281
  have eq48318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15494 x
       have i₂ := eq48282
       grind)
    | exact superpose eq48282 eq15494
    | exact resolve eq15494 eq48282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15494 eq48282
  have eq48458 : False := by grind
  exact eq48458

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq60
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90
  have eq454 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq481 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq485 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq481 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq481 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq481 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq495 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq485 X0 X1
       have j1 := eq84 X0 (σ X1)
       grind)
    | (have r₁ := eq485 X0 X1
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq485 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq485
  have eq502 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq495 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq495
    | (have j0 := eq495 X0 X1
       grind)
    | exact resolve eq495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq503 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq507 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq503 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq503
    | exact resolve eq503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq503 x y
       grind)
    | exact superpose eq503 eq16
    | exact resolve eq16 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq631 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq507 X0 (τ X1)
       grind)
    | exact superpose eq507 eq17
    | exact resolve eq17 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq507
  have eq659 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq631
    | exact resolve eq631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq673 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq659
    | exact resolve eq659 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq702 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq518
       have i₂ := eq673 x y
       grind)
    | exact superpose eq673 eq518
    | exact resolve eq518 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq673
  have eq703 : False := by grind
  exact eq703

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
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
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq53
    | exact resolve eq53 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq53
  have eq63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq98 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq113 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ X0) (σ X1)) (M.op X2 (M.op X2 (σ X1)))) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq74 X1 X0
       grind)
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq9
    | (have j1 := eq74 X1 X0
       grind)
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq74 X1 X0
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq13 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq487 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq468 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq491 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq487
    | (have j0 := eq487 X0 X1
       grind)
    | exact resolve eq487 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq492 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq491 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq503 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq492
    | (have j0 := eq492 X0 X1
       grind)
    | exact resolve eq492 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq492
  have eq510 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq503
    | (have j0 := eq503 X0 X1
       grind)
    | exact resolve eq503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq1034 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq98 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq98 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1388 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq1034 X0 x X1
       grind)
    | exact superpose eq1034 eq9
    | exact resolve eq9 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq2741 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq510
    | (have j0 := eq510 X0 (τ X1)
       grind)
    | exact resolve eq510 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2753 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 (τ X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq510
    | (have j0 := eq510 X1 (τ X0)
       grind)
    | exact resolve eq510 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq2905 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2753 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2753
    | (have j0 := eq2753 X0 X1
       grind)
    | exact resolve eq2753 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq2913 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2741 X0 X1
       have i₂ := eq58 X1
       grind)
    | exact superpose eq58 eq2741
    | (have j0 := eq2741 X0 X1
       grind)
    | exact resolve eq2741 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq2933 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2905 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2905
    | (have j0 := eq2905 X0 X1
       grind)
    | exact resolve eq2905 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq2941 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2913 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2913
    | (have j0 := eq2913 X0 X1
       grind)
    | exact resolve eq2913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913
  have eq2960 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2933 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2933
    | (have j0 := eq2933 X0 X1
       grind)
    | exact resolve eq2933 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq2964 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2941 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2941
    | (have j0 := eq2941 X0 X1
       grind)
    | exact resolve eq2941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941
  have eq2973 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2960 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2960
    | (have j0 := eq2960 X0 X1
       grind)
    | exact resolve eq2960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960
  have eq2976 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2964 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2964
    | (have j0 := eq2964 X0 X1
       grind)
    | exact resolve eq2964 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964
  have eq2982 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2973 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq2973 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2973 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2973
  have eq2985 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2976 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2976
    | (have j0 := eq2976 X0 X1
       grind)
    | exact resolve eq2976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq2991 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2985 X0 X1
       have i₂ := eq58 X1
       grind)
    | exact superpose eq58 eq2985
    | (have j0 := eq2985 X0 X1
       grind)
    | exact resolve eq2985 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985
  have eq2992 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2991 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2991
    | (have j0 := eq2991 X0 X1
       grind)
    | exact resolve eq2991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2991
  have eq2993 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2992 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq2992 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2992 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3137 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993
  have eq3769 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq486
    | (have j0 := eq486 X1 X1
       grind)
    | exact resolve eq486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq3804 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3769 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3769
    | (have j0 := eq3769 X0 X1
       grind)
    | exact resolve eq3769 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769
  have eq3808 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3804 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3804
    | (have j0 := eq3804 X0 X1
       grind)
    | exact resolve eq3804 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3804
  have eq3812 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq3808 X0 X1
       have j1 := eq113 X1 X0
       grind)
    | (have r₁ := eq3808 (σ X0) X0
       have r₂ := eq113 X0 (σ X0)
       grind)
    | (have r₁ := eq3808 X0 X0
       have r₂ := eq113 X0 X1
       grind)
    | exact resolve eq3808 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq3808
  have eq7886 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq465 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq465
    | exact resolve eq465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq8027 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7886 X0 X1 X2
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq7886
    | (have j0 := eq7886 X0 X1 X2
       grind)
    | exact resolve eq7886 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq7886
  have eq8037 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8027 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq8027
    | (have j0 := eq8027 X0 X1 X2
       grind)
    | exact resolve eq8027 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8027
  have eq8041 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8037 X0 X1 X2
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq8037 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq8037 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037
  have eq54645 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3812 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3812
    | exact resolve eq3812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq54748 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54645 X0 (σ X1)
       have i₂ := eq2982 X0 X1
       grind)
    | exact superpose eq2982 eq54645
    | (have j0 := eq54645 X0 (σ X1)
       have j1 := eq2982 X0 X1
       grind)
    | (have r₁ := eq54645 (σ X1) (σ X1)
       have r₂ := eq2982 (σ X1) X1
       grind)
    | exact resolve eq54645 eq2982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982 eq54645
  have eq54765 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54748 X0 X1
       have j1 := eq3137 (σ X1) X0
       grind)
    | (have r₁ := eq54748 X1 X1
       have r₂ := eq3137 (σ X1) X1
       grind)
    | (have r₁ := eq54748 (σ X1) X1
       have r₂ := eq3137 (σ X1) (σ X1)
       grind)
    | exact resolve eq54748 eq3137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3137 eq54748
  have eq82060 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1388 X0 (σ X1) (M.op x (M.op x X0))
       have i₂ := eq8041 X0 X1 x
       grind)
    | exact superpose eq8041 eq1388
    | (have j1 := eq8041 X0 X1 x
       grind)
    | exact resolve eq1388 eq8041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq8041
  have eq82397 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82060 X0 X1
       have j1 := eq54765 X0 X1
       grind)
    | (have r₁ := eq82060 X0 X1
       have r₂ := eq54765 X0 X1
       grind)
    | (have r₁ := eq82060 (σ X1) X1
       have r₂ := eq54765 (σ X1) X1
       grind)
    | exact resolve eq82060 eq54765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54765 eq82060
  have eq82526 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82397 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82397
    | exact resolve eq82397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82576 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq82397 (σ X0) X1
       grind)
    | exact superpose eq82397 eq15
    | exact resolve eq15 eq82397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82397
  have eq84445 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82576 x y
       grind)
    | exact superpose eq82576 eq16
    | exact resolve eq16 eq82576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82576
  have eq85004 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq84445
       have i₂ := eq82526 y x
       grind)
    | exact superpose eq82526 eq84445
    | exact resolve eq84445 eq82526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82526 eq84445
  have eq85005 : False := by grind
  exact eq85005

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq247 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq61 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq61 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq345 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 (M.op X1 x)
       have i₂ := eq247 X1 x X0
       grind)
    | exact superpose eq247 eq9
    | exact resolve eq9 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq709 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq709 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq5844 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq756 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq5845 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5844 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5844
  have eq5885 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq5845 (σ X0) X1
       grind)
    | exact superpose eq5845 eq28
    | (have j1 := eq5845 (σ X0) X1
       grind)
    | exact resolve eq28 eq5845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq5886 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq5845 (τ X0) X1
       grind)
    | exact superpose eq5845 eq18
    | (have j1 := eq5845 (τ X0) X1
       grind)
    | exact resolve eq18 eq5845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5968 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq5845 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq5845 (M.op X1 X1) X1
       grind)
    | exact superpose eq5845 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq5845 X2 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq5845 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq5845 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq5845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5845
  have eq6239 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = X0 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0
       have i₂ := eq5885 X0 X1
       grind)
    | exact superpose eq5885 eq10
    | (have j1 := eq5885 X0 X1
       grind)
    | exact resolve eq10 eq5885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5885
  have eq6506 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5886 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5886
    | exact resolve eq5886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886
  have eq6684 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6506 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6506
    | (have j0 := eq6506 X0 X1
       grind)
    | exact resolve eq6506 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6506
  have eq8164 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq6239 X0 X1
       grind)
    | exact superpose eq6239 eq11
    | (have j1 := eq6239 X0 X1
       grind)
    | exact resolve eq11 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239
  have eq8173 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8164 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq8164
    | (have j0 := eq8164 X0 X1
       grind)
    | exact resolve eq8164 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8164
  have eq8555 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8173 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8173
    | (have j0 := eq8173 (τ X0) X1
       grind)
    | exact resolve eq8173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq12467 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5968 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq12496 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12467 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12467
  have eq12497 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12496 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12496
  have eq12505 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12497 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12497
    | exact resolve eq12497 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12506 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12497 (τ X0)
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq12497
    | exact resolve eq12497 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq12515 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12506 X0
       have i₂ := eq12497 X0
       grind)
    | exact superpose eq12497 eq12506
    | exact resolve eq12506 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12516 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12505 X0
       have i₂ := eq12497 X0
       grind)
    | exact superpose eq12497 eq12505
    | exact resolve eq12505 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12497 eq12505
  have eq12568 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq12515 X0
       grind)
    | exact superpose eq12515 eq9
    | exact resolve eq9 eq12515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12599 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) (τ X0) x
       have i₂ := eq12515 X0
       grind)
    | exact superpose eq12515 eq345
    | exact resolve eq345 eq12515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq12515
  have eq12695 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8555 X1 (σ X0)
       have i₂ := eq12516 X0
       grind)
    | exact superpose eq12516 eq8555
    | (have j0 := eq8555 X1 (σ X0)
       grind)
    | exact resolve eq8555 eq12516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8555
  have eq12700 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq12516 X0
       grind)
    | exact superpose eq12516 eq9
    | exact resolve eq9 eq12516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12766 : ∀ X0 X1 : G, (τ X1) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12695 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq12695
    | (have j0 := eq12695 X0 X1
       grind)
    | exact resolve eq12695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12695
  have eq13528 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12599 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq12599
    | exact resolve eq12599 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12599
  have eq14150 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op (τ (σ X0)) X1) (τ (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq13528 (σ X0) X1
       have i₂ := eq12516 X0
       grind)
    | exact superpose eq12516 eq13528
    | exact resolve eq13528 eq12516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12516 eq13528
  have eq14236 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14150 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14150
    | exact resolve eq14150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14150
  have eq14701 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (σ (M.op X0 X0))))) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12568 (M.op (σ X0) (σ (M.op X0 X0))) (M.op X0 X1)
       have i₂ := eq14236 X0 X1
       grind)
    | exact superpose eq14236 eq12568
    | exact resolve eq12568 eq14236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12568 eq14236
  have eq14770 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (τ (σ X0)) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14701 X0 X1
       have i₂ := eq12700 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq12700 eq14701
    | exact resolve eq14701 eq12700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12700 eq14701
  have eq14781 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14770 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14770
    | exact resolve eq14770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14770
  have eq14786 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14781 X0 x
       have i₂ := eq60 X0 X0 x
       grind)
    | exact superpose eq60 eq14781
    | exact resolve eq14781 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq14781
  have eq15212 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ (M.op X0 X0)))
       have i₂ := eq14786 X0
       grind)
    | exact superpose eq14786 eq11
    | exact resolve eq11 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14786
  have eq16843 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12766 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12766
    | (have j0 := eq12766 X1 (σ X0)
       grind)
    | exact resolve eq12766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12766
  have eq17125 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16843 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq16843
    | (have j0 := eq16843 X0 X1
       grind)
    | exact resolve eq16843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16843
  have eq17983 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17125 y x
       grind)
    | exact superpose eq17125 eq16
    | (have j1 := eq17125 y x
       grind)
    | exact resolve eq16 eq17125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17125
  have eq18238 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17983
       have i₂ := eq6684 y x
       grind)
    | exact superpose eq6684 eq17983
    | (have j1 := eq6684 y x
       grind)
    | (have r₁ := eq17983
       have r₂ := eq6684 y x
       grind)
    | exact resolve eq17983 eq6684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684 eq17983
  have eq18243 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq18238
  have eq18244 : y = (M.op x x) := by grind
  clear eq18243
  have eq18274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15212 x
       have i₂ := eq18244
       grind)
    | exact superpose eq18244 eq15212
    | exact resolve eq15212 eq18244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15212 eq18244
  have eq20500 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18274
       grind)
    | exact superpose eq18274 eq16
    | (have r₁ := eq16
       have r₂ := eq18274
       grind)
    | exact resolve eq16 eq18274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18274
  have eq20564 : False := by grind
  exact eq20564

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_pyx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 X1 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq16 X0 x x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X2 X3 : G, (M.op x y) = (M.op x (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq192 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 (k X0 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X3 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op X2 (M.op X3 X0))) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
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
  have eq635 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq640 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq630
       grind)
    | exact superpose eq630 eq41
    | exact resolve eq41 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq630
  have eq643 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq642
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq642
    | exact resolve eq642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq645 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq643
    | exact resolve eq643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq635
    | exact resolve eq635 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq662 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq655
       have r₂ := eq27
       grind)
    | exact resolve eq655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq667 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq662 eq176
    | exact resolve eq176 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq668 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq662 eq181
    | exact resolve eq181 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq670 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq13
    | exact resolve eq13 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq668
       have r₂ := eq670
       grind)
    | exact resolve eq668 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq670
  have eq679 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq673 eq98
    | exact resolve eq98 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq726 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq720
    | exact resolve eq720 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq731 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq640 x
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq640
    | (have j0 := eq640 x
       grind)
    | exact resolve eq640 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq667
    | (have j0 := eq667 (σ x)
       grind)
    | exact resolve eq667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq752 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq739 eq192
    | exact resolve eq192 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq739
  have eq1189 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq610 x x X0 X1
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq610
    | (have j0 := eq610 x x x x
       grind)
    | exact resolve eq610 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X0)) = (M.op X1 (k X2 X0)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 (k X2 X0) X3 (M.op X0 x)
       have i₂ := eq610 X2 X0 x X1
       grind)
    | exact superpose eq610 eq177
    | (have j1 := eq610 X2 X0 X2 X3
       grind)
    | exact resolve eq177 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1216 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1189 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | (have i₁ := eq1189 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | exact superpose eq698 eq1189
    | (have j0 := eq1189 X0 x
       grind)
    | exact resolve eq1189 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1218 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq28 eq1216
    | (have j0 := eq1216 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq1216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1219 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq726 eq1218
    | (have j0 := eq1218 X0
       grind)
    | exact resolve eq1218 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1223 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq611 x x X0 X1
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq611
    | (have j0 := eq611 x x x x
       grind)
    | exact resolve eq611 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq1223
    | (have j0 := eq1223 X0 X1
       have j1 := eq28 x x
       grind)
    | exact resolve eq1223 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1326 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1202 eq1320
    | (have j1 := eq1202 x x x x
       grind)
    | exact resolve eq1320 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1327 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq726 eq1326
    | (have j0 := eq1326 X0
       grind)
    | exact resolve eq1326 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq1326
  have eq1433 : ∀ X1 : G, y = (M.op x (M.op X1 (M.op x y))) ∨ x = y ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq178 (M.op x (k x x)) X1
       have i₂ := eq1327 x
       grind)
    | exact superpose eq1327 eq178
    | exact resolve eq178 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1451 : x = (M.op y (M.op x y)) ∨ x = y ∨ y = (k x x) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq1433 eq1219
    | exact resolve eq1219 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq1433
  have eq1464 : y = (k x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by grind
  clear eq1451
  have eq1473 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq611 x x X0 X1
       have i₂ := eq1464
       grind)
    | exact superpose eq1464 eq611
    | (have j0 := eq611 x x x x
       grind)
    | exact resolve eq611 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1202 eq1473
    | (have j1 := eq1202 x x x x
       grind)
    | exact resolve eq1473 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1479 : ∀ X0 : G, x = (M.op y (M.op X0 y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1464 eq1476
    | exact resolve eq1476 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464 eq1476
  have eq1482 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1479 x
       have i₂ := eq698 y x
       grind)
    | (have i₁ := eq1479 x
       have i₂ := eq698 y x
       grind)
    | exact superpose eq698 eq1479
    | (have j0 := eq1479 x
       grind)
    | exact resolve eq1479 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1483 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq1482
  have eq1502 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1483 eq178
    | exact resolve eq178 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1521 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1483 eq1502
    | exact resolve eq1502 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483 eq1502
  have eq1537 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq1521
  have eq1544 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1537
       have r₂ := eq731
       grind)
    | exact resolve eq1537 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq1537
  have eq1553 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 x
       have i₂ := eq1544
       grind)
    | exact superpose eq1544 eq16
    | exact resolve eq16 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1563 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1553 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | (have i₁ := eq1553 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | exact superpose eq698 eq1553
    | (have j0 := eq1553 X0 x
       grind)
    | exact resolve eq1553 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq3252 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq679
    | exact resolve eq679 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq3362 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq3252
    | exact resolve eq3252 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq3459 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3362 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3362
       grind)
    | exact resolve eq13 eq3362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3472 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3459
  have eq3485 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq3472
    | exact resolve eq3472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq3490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq3485
    | exact resolve eq3485 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3485
  have eq3491 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3490
       have r₂ := eq27
       grind)
    | exact resolve eq3490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490
  have eq3494 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3491 eq669
    | exact resolve eq669 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq3504 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3491 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3506 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ (M.op x y)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq3491 eq16
    | exact resolve eq16 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3523 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3494
  have eq3528 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq3504
    | exact resolve eq3504 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504
  have eq3532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq3528
    | exact resolve eq3528 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq3528
  have eq3535 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3532
       have r₂ := eq27
       grind)
    | exact resolve eq3532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3546 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3523 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq28 eq3523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq4194 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3546 eq132
    | exact resolve eq132 eq3546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq4208 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq4194
    | exact resolve eq4194 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4194
  have eq4341 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ y = (M.op x x) ∨ y = (k (M.op x y) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4208 eq3506
    | exact resolve eq3506 eq4208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506 eq4208
  have eq4358 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ y = (M.op x x) ∨ y = (k (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq4341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq9308 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (k (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq4358
    | exact resolve eq4358 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq4358
  have eq9387 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (k (M.op x y) x) := by grind
  clear eq9308
  have eq9414 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (k (M.op x y) x) := by
    first
    | exact superpose eq9387 eq3491
    | exact resolve eq3491 eq9387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491 eq9387
  have eq9459 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (k (M.op x y) x) := by grind
  clear eq9414
  have eq9473 : y = (k (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9459
       have r₂ := eq3535
       grind)
    | exact resolve eq9459 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9459
  have eq9483 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq9473 eq610
    | (have j0 := eq610 (M.op x y) x x x
       grind)
    | exact resolve eq610 eq9473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9473
  have eq9484 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9483 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | (have i₁ := eq9483 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | exact superpose eq698 eq9483
    | (have j0 := eq9483 X0 x
       grind)
    | exact resolve eq9483 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq9483
  have eq9489 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1563 eq9484
    | (have j0 := eq9484 X0
       have j1 := eq1563 X0
       grind)
    | exact resolve eq9484 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq9484
  have eq9618 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq188 eq9489
    | (have j0 := eq9489 y
       grind)
    | exact resolve eq9489 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq9489
  have eq9680 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq9618
  have eq9700 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq9680 eq13
    | exact resolve eq13 eq9680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9703 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9680 eq28
    | exact resolve eq28 eq9680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9680
  have eq9722 : x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq9700
       have r₂ := eq9703
       grind)
    | exact resolve eq9700 eq9703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9700 eq9703
  have eq9728 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq9722 eq42
    | exact resolve eq42 eq9722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq9734 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq9728
    | exact resolve eq9728 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9728
  have eq9737 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq9734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9734
    | exact resolve eq9734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9734
  have eq9745 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq9737 eq640
    | (have j0 := eq640 (σ (M.op x y))
       grind)
    | exact resolve eq640 eq9737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq9747 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq9737 eq611
    | (have j0 := eq611 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq611 eq9737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9749 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1202 eq9747
    | (have j1 := eq1202 (σ (M.op x y)) x (σ (M.op x y)) x
       grind)
    | exact resolve eq9747 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9747
  have eq9755 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9737 eq9749
    | exact resolve eq9749 eq9737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9749
  have eq11594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq9755 eq752
    | exact resolve eq752 eq9755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq11642 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11594
       have r₂ := eq27
       grind)
    | exact resolve eq11594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11594
  have eq11709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11642 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq11642
       grind)
    | exact resolve eq13 eq11642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11642
  have eq11725 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq11709
  have eq11749 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9737 eq11725
    | exact resolve eq11725 eq9737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11725
  have eq11766 : y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11749
       have r₂ := eq3535
       grind)
    | exact resolve eq11749 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535 eq11749
  have eq11806 : y = (k x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq11766
       grind)
    | exact superpose eq11766 eq28
    | exact resolve eq28 eq11766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11766
  have eq11820 : y = (k x x) ∨ x = y := by grind
  clear eq11806
  have eq11856 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq11820
       grind)
    | exact superpose eq11820 eq40
    | exact resolve eq40 eq11820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11868 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11856
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11856
    | exact resolve eq11856 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11856
  have eq11873 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11868
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11868
    | exact resolve eq11868 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11868
  have eq11934 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq11873 eq611
    | (have j0 := eq611 (σ x) (σ x) x x
       grind)
    | exact resolve eq611 eq11873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq11935 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq11873 eq610
    | (have j0 := eq610 (σ x) (σ x) x x
       grind)
    | exact resolve eq610 eq11873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq11936 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq699 eq11935
    | (have j0 := eq11935 X0 (σ x)
       grind)
    | exact resolve eq11935 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11935
  have eq11937 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1202 eq11934
    | (have j1 := eq1202 (σ x) x (σ x) x
       grind)
    | exact resolve eq11934 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq11934
  have eq11941 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11873 eq11937
    | exact resolve eq11937 eq11873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11873 eq11937
  have eq11944 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq699 eq11941
    | (have j0 := eq11941 (σ x)
       grind)
    | exact resolve eq11941 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq11941
  have eq12925 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11944 eq179
    | exact resolve eq179 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq11944
  have eq14231 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq11936
    | (have j0 := eq11936 (σ y)
       grind)
    | exact resolve eq11936 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11936
  have eq14476 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq14231 eq12925
    | exact resolve eq12925 eq14231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12925 eq14231
  have eq14527 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq14476
  have eq14571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq14527 eq9755
    | exact resolve eq9755 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14527
  have eq14593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14571
  have eq14604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq14593
    | exact resolve eq14593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14593
  have eq14608 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq14604
       have r₂ := eq27
       grind)
    | exact resolve eq14604 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604
  have eq14640 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14608 eq9755
    | exact resolve eq9755 eq14608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9755
  have eq14661 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq14640
  have eq14670 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14608 eq14661
    | exact resolve eq14661 eq14608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14608 eq14661
  have eq14672 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq14670
       have r₂ := eq9745
       grind)
    | exact resolve eq14670 eq9745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9745 eq14670
  have eq14689 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14672 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq14672
       grind)
    | exact resolve eq13 eq14672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14672
  have eq14706 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq14689
  have eq14713 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq9737 eq14706
    | exact resolve eq14706 eq9737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9737 eq14706
  have eq14791 : (M.op x y) = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq14713 eq29
    | exact resolve eq29 eq14713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq14797 : (k (M.op x y) x) = (τ (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq14713 eq132
    | exact resolve eq132 eq14713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq14713
  have eq14875 : (k x x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq98 eq14797
    | exact resolve eq14797 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq14797
  have eq14881 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq14791
    | exact resolve eq14791 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14791
  have eq14883 : y = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq11820 eq14875
    | exact resolve eq14875 eq11820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11820 eq14875
  have eq14886 : y = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14881 eq14883
    | exact resolve eq14883 eq14881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14881 eq14883
  have eq14888 : x = y ∨ x = y := by
    first
    | exact superpose eq9722 eq14886
    | exact resolve eq14886 eq9722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9722 eq14886
  have eq14889 : x = y := by grind
  clear eq14888
  have eq14892 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14889
       grind)
    | exact superpose eq14889 eq18
    | exact resolve eq18 eq14889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14893 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14889
       grind)
    | exact superpose eq14889 eq24
    | exact resolve eq24 eq14889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14889
  have eq14924 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14893
    | exact resolve eq14893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14893
  have eq14925 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14924 eq26
    | exact resolve eq26 eq14924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14924
  have eq15088 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq14892
       grind)
    | exact superpose eq14892 eq13
    | exact resolve eq13 eq14892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15091 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq14892
       grind)
    | exact superpose eq14892 eq28
    | exact resolve eq28 eq14892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14892
  have eq15109 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq15088
       have r₂ := eq15091
       grind)
    | exact resolve eq15088 eq15091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15088 eq15091
  have eq15635 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14925 eq13
    | exact resolve eq13 eq14925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15638 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14925 eq28
    | exact resolve eq28 eq14925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq14925
  have eq15655 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq15635
       have r₂ := eq15638
       grind)
    | exact resolve eq15635 eq15638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15635 eq15638
  have eq15692 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq15109
       grind)
    | exact superpose eq15109 eq40
    | exact resolve eq40 eq15109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15109
  have eq15699 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15692
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15692
    | exact resolve eq15692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15692
  have eq15701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15655 eq15699
    | exact resolve eq15699 eq15655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655 eq15699
  have eq15703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15701
    | exact resolve eq15701 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15701
  have eq15705 : False := by grind
  exact eq15705

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq54
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq59 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq59
  have eq198 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq203 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq198 X1 X0
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq198 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq198 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq198
  have eq254 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq203 (σ X1) (σ X0)
       grind)
    | exact superpose eq203 eq15
    | exact resolve eq15 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq203 X1 X0
       grind)
    | exact superpose eq203 eq254
    | exact resolve eq254 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq254
  have eq261 : False := by grind
  exact eq261

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_y_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq30 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq34 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq35 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq29
    | (have j0 := eq29 (M.op x y)
       grind)
    | exact resolve eq29 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
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
  have eq42 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
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
  have eq53 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0 X1
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 X1 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y X0 X1 x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq85 : (M.op y (M.op x y)) = (k y (M.op y (M.op x y))) := by grind
  have eq91 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq68 eq105
    | exact resolve eq105 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq121 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq131 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq14 sF3 (σ X0)
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ y) (σ X0)
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq133 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq68
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq134 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq133
    | exact resolve eq133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq136 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq134
    | exact resolve eq134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq170 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq49
  have eq211 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq170 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq170
    | exact resolve eq170 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq240 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq211
  have eq302 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq39 eq240
    | exact resolve eq240 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq35
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq35
    | (have j1 := eq106 (σ (M.op x y))
       grind)
    | exact resolve eq35 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq368 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq42
    | (have j1 := eq106 (σ x)
       grind)
    | exact resolve eq42 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq414 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq416 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq59
  have eq1475 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq368
       grind)
    | exact superpose eq368 eq10
    | exact resolve eq10 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2064 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq121
  have eq11615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq136
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq136
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq136 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11615
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11615
    | exact resolve eq11615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11615
  have eq11640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq11637
    | exact resolve eq11637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11637
  have eq11641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11640
       have r₂ := eq28
       grind)
    | exact resolve eq11640 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11640
  have eq11642 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11641
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11641
    | exact resolve eq11641 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11641
  have eq11645 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11642 eq107
    | (have r₁ := eq107
       have r₂ := eq11642
       grind)
    | exact resolve eq107 eq11642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11675 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq11642
  have eq11677 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq11645
  have eq11683 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11677
       have r₂ := eq11675
       grind)
    | exact resolve eq11677 eq11675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11675 eq11677
  have eq11958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11683
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq11683
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq11683 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11683
  have eq11977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq11958
  have eq11981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11977
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11977
    | exact resolve eq11977 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11977
  have eq11984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq11981
    | exact resolve eq11981 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11981
  have eq11985 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq11984
       have r₂ := eq28
       grind)
    | exact resolve eq11984 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11984
  have eq11986 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11985
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11985
    | exact resolve eq11985 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11985
  have eq11987 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq11986
  have eq11989 : x = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11987 eq302
    | exact resolve eq302 eq11987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11992 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11987 eq1475
    | exact resolve eq1475 eq11987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq11987
  have eq12037 : y = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq11992
    | exact resolve eq11992 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992
  have eq12040 : x = (k y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq11989
    | exact resolve eq11989 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11989
  have eq12102 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq12040
       grind)
    | exact superpose eq12040 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq12040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12040
  have eq12103 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq12102
  have eq12106 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12103
    | exact resolve eq12103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12103
  have eq12109 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12106
    | exact resolve eq12106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12106
  have eq12110 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12109
  have eq12120 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq12110
       grind)
    | exact superpose eq12110 eq103
    | (have r₁ := eq103
       have r₂ := eq12110
       grind)
    | exact resolve eq103 eq12110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12131 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq12110
       grind)
    | exact superpose eq12110 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq12110
       grind)
    | exact resolve eq13 eq12110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12149 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12110
  have eq12151 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (M.op x x) := by grind
  clear eq12131
  have eq12152 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12151
  have eq12154 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12120
  have eq12156 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12154
       have r₂ := eq12149
       grind)
    | exact resolve eq12154 eq12149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12149 eq12154
  have eq12169 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq368
       have i₂ := eq12152
       grind)
    | exact superpose eq12152 eq368
    | exact resolve eq368 eq12152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12200 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq12169
    | exact resolve eq12169 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12169
  have eq12207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq136
       have i₂ := eq12156
       grind)
    | exact superpose eq12156 eq136
    | exact resolve eq136 eq12156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq12218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq12207
    | exact resolve eq12207 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12207
  have eq12220 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12218
       have r₂ := eq28
       grind)
    | exact resolve eq12218 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12218
  have eq22641 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq2064 X0
       grind)
    | exact superpose eq2064 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq2064 X0
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq2064 X0
       grind)
    | exact resolve eq13 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22664 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22667 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq22641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22641
  have eq22668 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq22667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22667
  have eq22671 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22668 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq22668
    | (have j0 := eq22668 X0
       grind)
    | exact resolve eq22668 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22668
  have eq22691 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq22671
  have eq22711 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq22691 X0
       have j1 := eq22664 X0
       grind)
    | (have r₁ := eq22691 X0
       have r₂ := eq22664 X0
       grind)
    | exact resolve eq22691 eq22664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22664 eq22691
  have eq59751 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq12037
       grind)
    | exact superpose eq12037 eq106
    | (have j0 := eq106 x
       grind)
    | exact resolve eq106 eq12037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12037
  have eq59761 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq59751
  have eq60909 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq59761
       grind)
    | exact superpose eq59761 eq103
    | (have r₁ := eq103
       have r₂ := eq59761
       grind)
    | exact resolve eq103 eq59761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60985 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  have eq60986 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq59761
  have eq60989 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq60909
  have eq60997 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq60989
       have r₂ := eq60986
       grind)
    | exact resolve eq60989 eq60986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60986 eq60989
  have eq62570 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12200 eq240
    | exact resolve eq240 eq12200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62610 : x = (k x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39 eq62570
    | exact resolve eq62570 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62570
  have eq62622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12220 eq12200
    | exact resolve eq12200 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12200
  have eq62668 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq62622
  have eq62678 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62668
       have r₂ := eq28
       grind)
    | exact resolve eq62668 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62668
  have eq62684 : x = (k (τ (σ y)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62678 eq302
    | exact resolve eq302 eq62678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62678
  have eq62759 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40 eq62684
    | exact resolve eq62684 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62684
  have eq62871 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12156
       have i₂ := eq62759
       grind)
    | exact superpose eq62759 eq12156
    | exact resolve eq12156 eq62759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62759
  have eq62915 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62871
  have eq63012 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq63017 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2064 x
       have i₂ := eq62915
       grind)
    | exact superpose eq62915 eq2064
    | exact resolve eq2064 eq62915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064 eq62915
  have eq63093 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63017
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63017
    | exact resolve eq63017 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63017
  have eq63102 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63093
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq63093
    | exact resolve eq63093 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63093
  have eq63104 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq63102
    | exact resolve eq63102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63102
  have eq63106 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63104
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq63104
    | exact resolve eq63104 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63104
  have eq63108 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63106
    | exact resolve eq63106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63106
  have eq63110 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq63108
    | exact resolve eq63108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63108
  have eq63111 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq63110
  have eq63113 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63111
    | exact resolve eq63111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63111
  have eq63115 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63113
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq63113
    | exact resolve eq63113 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63113
  have eq70839 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63115 eq107
    | (have r₁ := eq107
       have r₂ := eq63115
       grind)
    | exact resolve eq107 eq63115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq70888 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq63115
  have eq70897 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq70839
  have eq70905 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq70897
       have r₂ := eq70888
       grind)
    | exact resolve eq70897 eq70888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70888 eq70897
  have eq89008 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70905
       have i₂ := eq63012
       grind)
    | exact superpose eq63012 eq70905
    | exact resolve eq70905 eq63012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63012 eq70905
  have eq89102 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq89008
  have eq89134 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89102
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq89102
    | exact resolve eq89102 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89102
  have eq89135 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq89134
  have eq89199 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq89135 eq9
    | exact resolve eq9 eq89135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89208 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq89135 eq414
    | exact resolve eq414 eq89135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89135
  have eq89249 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq416 eq89199
    | (have j0 := eq89199 X0 (σ x)
       grind)
    | exact resolve eq89199 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89199
  have eq154847 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12152
       have i₂ := eq62610
       grind)
    | exact superpose eq62610 eq12152
    | exact resolve eq12152 eq62610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12152 eq62610
  have eq154888 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq154847
  have eq154909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12220 eq154888
    | exact resolve eq154888 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12220 eq154888
  have eq155025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq154909
  have eq155041 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq155025
       have r₂ := eq28
       grind)
    | exact resolve eq155025 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155025
  have eq156012 : x = (k (τ (σ y)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq155041 eq302
    | exact resolve eq302 eq155041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq155041
  have eq156111 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq156012
    | exact resolve eq156012 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156012
  have eq156768 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12156
       have i₂ := eq156111
       grind)
    | exact superpose eq156111 eq12156
    | exact resolve eq12156 eq156111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12156
  have eq156783 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq60997
       have i₂ := eq156111
       grind)
    | exact superpose eq156111 eq60997
    | exact resolve eq60997 eq156111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60997 eq156111
  have eq156823 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq156783
  have eq156836 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq156768
  have eq156852 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq156823
       have r₂ := eq60985
       grind)
    | exact resolve eq156823 eq60985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60985 eq156823
  have eq156895 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq156836
       grind)
    | exact superpose eq156836 eq53
    | exact resolve eq53 eq156836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156939 : x = (k y x) ∨ x = (M.op x y) := by grind
  have eq156945 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq156836
       grind)
    | exact superpose eq156836 eq13
    | exact resolve eq13 eq156836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156836
  have eq156966 : y = (k x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq156945
  have eq157021 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq156895 x
       have i₂ := eq415 sF0 x
       grind)
    | (have i₁ := eq156895 x
       have i₂ := eq415 sF0 x
       grind)
    | exact superpose eq415 eq156895
    | (have j0 := eq156895 x
       grind)
    | exact resolve eq156895 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156895
  have eq157247 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op X1 x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq157021 eq9
    | exact resolve eq9 eq157021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157248 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq157021 eq13
    | exact resolve eq13 eq157021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157270 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq157248
  have eq157271 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq157270
  have eq157302 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq157271 eq367
    | exact resolve eq367 eq157271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157350 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157302
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq157302
    | exact resolve eq157302 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157302
  have eq159006 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq368
       have i₂ := eq156966
       grind)
    | exact superpose eq156966 eq368
    | exact resolve eq368 eq156966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq159078 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159006
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq159006
    | exact resolve eq159006 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159006
  have eq161290 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq157021 eq157247
    | exact resolve eq157247 eq157021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157021 eq157247
  have eq161551 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq161290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161290
  have eq164630 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq156852
       grind)
    | exact superpose eq156852 eq53
    | exact resolve eq53 eq156852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq164703 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq156852
  have eq164729 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq164630 x
       have i₂ := eq415 sF0 x
       grind)
    | (have i₁ := eq164630 x
       have i₂ := eq415 sF0 x
       grind)
    | exact superpose eq415 eq164630
    | (have j0 := eq164630 x
       grind)
    | exact resolve eq164630 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq164630
  have eq165732 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq157350 eq9
    | exact resolve eq9 eq157350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165741 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq157350 eq414
    | exact resolve eq414 eq157350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq157350
  have eq242456 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq159078 eq60
    | exact resolve eq60 eq159078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq159078
  have eq242483 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq416 eq242456
    | (have j0 := eq242456 (σ x)
       grind)
    | exact resolve eq242456 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq242456
  have eq302455 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq165732 eq89249
    | exact resolve eq89249 eq165732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89249 eq165732
  have eq302479 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq302455
  have eq302651 : ∀ X0 X1 : G, (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq165741 eq240
    | (have j1 := eq165741 X0 X1
       grind)
    | exact resolve eq240 eq165741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165741
  have eq302672 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq38 eq302651
    | (have j0 := eq302651 X0 X1
       grind)
    | exact resolve eq302651 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302651
  have eq316657 : ∀ X0 X1 : G, x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq302672 eq157271
    | (have j1 := eq302672 X0 X1
       grind)
    | exact resolve eq157271 eq302672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302672
  have eq316686 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq316657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316657
  have eq316734 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq316686 eq9
    | exact resolve eq9 eq316686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316686
  have eq317118 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f317118_15 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
      intro X0 X1
      grind
    have f317118_16 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
      intro X0 X1
      grind
    have f317118_25 : (σ (M.op x y)) ≠ (M.op (M.op (σ (M.op x y)) X0) (σ y)) := by grind
    have f317118_26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f317118_28 : x ≠ (M.op x y) := by grind
    have f317118_30 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) := by
      intro X0 X1
      first
      | (have j0 := f317118_16 X0 X1
         grind)
      | (have r₁ := f317118_16 X0 X1
         have r₂ := f317118_28
         grind)
      | exact resolve f317118_16 f317118_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f317118_31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
      intro X0 X1
      first
      | (have j0 := f317118_15 X0 X1
         grind)
      | (have r₁ := f317118_15 X0 X1
         have r₂ := f317118_26
         grind)
      | exact resolve f317118_15 f317118_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f317118_32 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f317118_31 X0 X1
         grind)
      | (have r₁ := f317118_31 X0 X1
         have r₂ := f317118_28
         grind)
      | exact resolve f317118_31 f317118_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f317118_69 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) := by
      intro X0
      first
      | (have i₁ := f317118_32 (M.op (σ (M.op x y)) X0) x
         have i₂ := f317118_30 x X0
         grind)
      | exact superpose f317118_30 f317118_32
      | exact resolve f317118_32 f317118_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f317118_446 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
      first
      | (have i₁ := f317118_25
         have i₂ := f317118_69 X0
         grind)
      | exact superpose f317118_69 f317118_25
      | (have r₁ := f317118_25
         have r₂ := f317118_69 X0
         grind)
      | exact resolve f317118_25 f317118_69
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f317118_455 : False := by grind
    exact f317118_455
  clear eq89208 eq316734
  have eq317173 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq317118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317118
  have eq317899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq302479 eq317173
    | exact resolve eq317173 eq302479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302479 eq317173
  have eq318057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq317899
  have eq318073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq318057
    | exact resolve eq318057 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318057
  have eq318078 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq318073
       have r₂ := eq28
       grind)
    | exact resolve eq318073 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318073
  have eq318115 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq318078 eq240
    | exact resolve eq240 eq318078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318078
  have eq318158 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38 eq318115
    | exact resolve eq318115 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318115
  have eq318277 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq318158 eq157271
    | exact resolve eq157271 eq318158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157271 eq318158
  have eq318653 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq318277
  have eq318771 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq318653 eq91
    | exact resolve eq91 eq318653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq318811 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq318653 eq242483
    | exact resolve eq242483 eq318653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242483
  have eq318824 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq318811
  have eq318952 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq318771
    | (have j0 := eq318771 (σ y)
       grind)
    | exact resolve eq318771 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318771
  have eq320788 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq318824 eq240
    | exact resolve eq240 eq318824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318824
  have eq320871 : x = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq320788
    | exact resolve eq320788 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320788
  have eq320957 : x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq156966
       have i₂ := eq320871
       grind)
    | exact superpose eq320871 eq156966
    | exact resolve eq156966 eq320871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156966 eq320871
  have eq321053 : x = (M.op x y) ∨ x = y := by grind
  clear eq320957
  have eq321341 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq321053 eq164729
    | exact resolve eq164729 eq321053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164729 eq321053
  have eq321658 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq321341
  have eq321685 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq321658
       have r₂ := eq164703
       grind)
    | exact resolve eq321658 eq164703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164703 eq321658
  have eq322001 : x ≠ (M.op x y) ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq321685
       grind)
    | exact superpose eq321685 eq103
    | exact resolve eq103 eq321685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq322119 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq161551 x
       have i₂ := eq321685
       grind)
    | exact superpose eq321685 eq161551
    | exact resolve eq161551 eq321685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322151 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22711 x
       have i₂ := eq321685
       grind)
    | exact superpose eq321685 eq22711
    | exact resolve eq22711 eq321685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22711
  have eq322172 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq322151
  have eq322197 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq322172
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq322172
    | exact resolve eq322172 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322172
  have eq322205 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq322001
       have r₂ := eq156939
       grind)
    | exact resolve eq322001 eq156939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156939 eq322001
  have eq326683 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq321685
       have i₂ := eq322119
       grind)
    | exact superpose eq322119 eq321685
    | exact resolve eq321685 eq322119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321685 eq322119
  have eq326887 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq326683
  have eq327127 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq326887 eq318952
    | exact resolve eq318952 eq326887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318952 eq326887
  have eq327129 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq327127
  have eq327435 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq318653 eq327129
    | exact resolve eq327129 eq318653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318653 eq327129
  have eq327539 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq327435
  have eq327718 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq327539 eq240
    | exact resolve eq240 eq327539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq327539
  have eq327803 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq327718
    | exact resolve eq327718 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq327718
  have eq327929 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq327803
       grind)
    | exact superpose eq327803 eq106
    | (have j0 := eq106 x
       grind)
    | exact resolve eq106 eq327803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq327803
  have eq327938 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq327929
  have eq328159 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq161551 x
       have i₂ := eq327938
       grind)
    | exact superpose eq327938 eq161551
    | exact resolve eq161551 eq327938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161551
  have eq328221 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq328159
  have eq328406 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq327938
       have i₂ := eq328221
       grind)
    | exact superpose eq328221 eq327938
    | exact resolve eq327938 eq328221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327938 eq328221
  have eq328610 : x = (M.op x y) := by grind
  clear eq328406
  have eq328671 : x = (M.op x y) := by
    first
    | exact superpose eq328610 eq19
    | exact resolve eq19 eq328610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq328672 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq328610 eq21
    | exact resolve eq21 eq328610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq328678 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq328610 eq38
    | exact resolve eq38 eq328610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq328684 : (M.op y x) = (k y (M.op y x)) := by
    first
    | exact superpose eq328610 eq85
    | exact resolve eq85 eq328610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq328702 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq328610 eq367
    | exact resolve eq367 eq328610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq328610
  have eq347512 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq328672
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq328672
    | exact resolve eq328672 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328672
  have eq347735 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq347512 eq23
    | exact resolve eq23 eq347512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq347736 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq347512 eq27
    | exact resolve eq27 eq347512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq354865 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq347512 eq322197
    | exact resolve eq322197 eq347512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322197
  have eq354866 : x = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq347512 eq322205
    | exact resolve eq322205 eq347512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322205
  have eq358643 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq347512 eq354865
    | exact resolve eq354865 eq347512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347512 eq354865
  have eq365026 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq131 x
       have i₂ := eq354866
       grind)
    | exact superpose eq354866 eq131
    | (have j0 := eq131 x
       grind)
    | exact resolve eq131 eq354866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq354866
  have eq365041 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq365026
       have i₂ := eq347735
       grind)
    | exact superpose eq347735 eq365026
    | exact resolve eq365026 eq347735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365026
  have eq365048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq347736 eq365041
    | exact resolve eq365041 eq347736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365041
  have eq365055 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq365048
       have r₂ := eq28
       grind)
    | exact resolve eq365048 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365048
  have eq365062 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq365055
       have i₂ := eq347735
       grind)
    | exact superpose eq347735 eq365055
    | exact resolve eq365055 eq347735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365055
  have eq365068 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq347736 eq365062
    | exact resolve eq365062 eq347736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365062
  have eq365074 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq365068
       have i₂ := eq347735
       grind)
    | exact superpose eq347735 eq365068
    | exact resolve eq365068 eq347735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365068
  have eq411808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq358643 eq365074
    | exact resolve eq365074 eq358643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358643 eq365074
  have eq411898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq411808
  have eq411912 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq411898
       have r₂ := eq28
       grind)
    | exact resolve eq411898 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411898
  have eq411918 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq411912 eq40
    | exact resolve eq40 eq411912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq411912
  have eq412003 : x = y ∨ x = y := by
    first
    | exact superpose eq328678 eq411918
    | exact resolve eq411918 eq328678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328678 eq411918
  have eq412004 : x = y := by grind
  clear eq412003
  have eq412007 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq412004
       grind)
    | exact superpose eq412004 eq25
    | exact resolve eq25 eq412004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq413877 : x = (M.op x x) := by
    first
    | (have i₁ := eq328671
       have i₂ := eq412004
       grind)
    | exact superpose eq412004 eq328671
    | exact resolve eq328671 eq412004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328671
  have eq413882 : (M.op x x) = (k x (M.op x x)) := by
    first
    | (have i₁ := eq328684
       have i₂ := eq412004
       grind)
    | exact superpose eq412004 eq328684
    | exact resolve eq328684 eq412004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328684 eq412004
  have eq421124 : x = (k x x) := by
    first
    | (have i₁ := eq413882
       have i₂ := eq413877
       grind)
    | exact superpose eq413877 eq413882
    | exact resolve eq413882 eq413877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413877 eq413882
  have eq421240 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq412007
       have i₂ := eq347735
       grind)
    | exact superpose eq347735 eq412007
    | exact resolve eq412007 eq347735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412007
  have eq422623 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq328702
       have i₂ := eq421124
       grind)
    | exact superpose eq421124 eq328702
    | exact resolve eq328702 eq421124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328702 eq421124
  have eq426955 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq421240 eq347736
    | exact resolve eq347736 eq421240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347736 eq421240
  have eq430788 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq422623
       have i₂ := eq347735
       grind)
    | exact superpose eq347735 eq422623
    | exact resolve eq422623 eq347735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347735 eq422623
  have eq430789 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq430788
  have eq432441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq426955 eq430789
    | exact resolve eq430789 eq426955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426955 eq430789
  have eq433859 : False := by grind
  exact eq433859

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq92
  have eq263 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | (have j0 := eq94 X1 X1
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq282 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq263
  have eq288 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq282 X0 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq282 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq282
  have eq292 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq288
    | (have j0 := eq288 X0 X1
       grind)
    | exact resolve eq288 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq288
  have eq650 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq292
    | exact resolve eq292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq722 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq650 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq650 X0 X1
       grind)
    | exact superpose eq650 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq650 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq650 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq650 X0 X1
       grind)
    | exact resolve eq13 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq748 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq742 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq742 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq742 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq809 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq813 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq809 X0 X1
       have j1 := eq650 X1 X0
       grind)
    | (have r₁ := eq809 X0 X0
       have r₂ := eq650 X0 X0
       grind)
    | (have r₁ := eq809 X1 X0
       have r₂ := eq650 X0 X1
       grind)
    | exact resolve eq809 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq809
  have eq947 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq813 (σ X1) (σ X0)
       grind)
    | exact superpose eq813 eq15
    | exact resolve eq15 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq947 X0 X1
       have i₂ := eq813 X1 X0
       grind)
    | exact superpose eq813 eq947
    | exact resolve eq947 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq947
  have eq1532 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq974 x y
       grind)
    | exact superpose eq974 eq16
    | (have r₁ := eq16
       have r₂ := eq974 x y
       grind)
    | exact resolve eq16 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1555 : False := by grind
  exact eq1555
