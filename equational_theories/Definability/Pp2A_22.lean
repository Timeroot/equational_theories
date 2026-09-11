import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation436 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law436 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq100
  have eq181 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq183 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq186 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq629 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq16
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1144 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq183
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1144 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1144
    | (have j0 := eq1144 X0 X1
       grind)
    | exact resolve eq1144 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq5273 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq629
       have i₂ := eq1195 y x
       grind)
    | exact superpose eq1195 eq629
    | (have j1 := eq1195 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq629
       have r₂ := eq1195 y x
       grind)
    | (have r₁ := eq629
       have r₂ := eq1195 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq629
       have r₂ := eq1195 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq629 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629 eq1195
  have eq5274 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5273
  have eq5276 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5274
       grind)
    | exact superpose eq5274 eq16
    | exact resolve eq16 eq5274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5274
  have eq5277 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5276
       have r₂ := eq80 x
       grind)
    | exact resolve eq5276 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq5284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq5277
       grind)
    | exact superpose eq5277 eq103
    | exact resolve eq103 eq5277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5277
  have eq5304 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5284
       have r₂ := eq16
       grind)
    | exact resolve eq5284 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5284
  have eq5307 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5304
       grind)
    | exact superpose eq5304 eq10
    | exact resolve eq10 eq5304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304
  have eq5362 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5307
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5307
    | exact resolve eq5307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5307
  have eq5365 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5362
       grind)
    | exact superpose eq5362 eq16
    | exact resolve eq16 eq5362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5362
  have eq5366 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5365
       have r₂ := eq80 x
       grind)
    | exact resolve eq5365 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq5365
  have eq5374 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5366
       grind)
    | exact superpose eq5366 eq10
    | exact resolve eq10 eq5366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366
  have eq5429 : y = (M.op x x) := by
    first
    | (have i₁ := eq5374
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5374
    | exact resolve eq5374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374
  have eq5442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq5429
       grind)
    | exact superpose eq5429 eq103
    | exact resolve eq103 eq5429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq5429
  have eq5461 : False := by grind
  exact eq5461

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
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
  have eq175 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 x X3 X4
       have i₂ := eq16 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op x X3) X3
       have i₂ := eq16 X0 x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
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
  have eq179 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq177 x X1 X3
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X3
    first
    | (have i₁ := eq181 x X3
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq181
    | exact resolve eq181 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq184 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq178
    | exact resolve eq178 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq200 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq191 eq183
    | exact resolve eq183 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq183 eq184
    | exact resolve eq184 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq224 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq191 eq220
    | exact resolve eq220 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq390 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq474 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq390
    | exact resolve eq390 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq837 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq200 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) y)
       have r₂ := eq200 (M.op (M.op x y) y)
       grind)
    | exact resolve eq28 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq838 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq883 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq838 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq838
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1003 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq974 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1816 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq883
       grind)
    | exact superpose eq883 eq40
    | exact resolve eq40 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq1817 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1816
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1816
    | exact resolve eq1816 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1819 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1817
    | exact resolve eq1817 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq16484 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq838 (M.op sF0 y)
       have i₂ := eq1003 (M.op sF0 y)
       grind)
    | exact superpose eq1003 eq838
    | (have j1 := eq1003 X0
       grind)
    | exact resolve eq838 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq16598 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16484 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16484 X0
       have r₂ := eq13 X0 (k X0 X0)
       grind)
    | (have r₁ := eq16484 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq16484 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq16484 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16484
  have eq16694 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq16598 X0
       grind)
    | exact superpose eq16598 eq178
    | exact resolve eq178 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq16701 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq838 X0
       have i₂ := eq16598 X0
       grind)
    | exact superpose eq16598 eq838
    | exact resolve eq838 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16713 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0 X0
       have i₂ := eq16598 X0
       grind)
    | exact superpose eq16598 eq186
    | exact resolve eq186 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16762 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16694 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16694
    | exact resolve eq16694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16694
  have eq16993 : ∀ X0 : G, (k (σ X0) (M.op (M.op x y) y)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq16701 (σ X0)
       grind)
    | exact superpose eq16701 eq10
    | exact resolve eq10 eq16701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16701
  have eq17130 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16713 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16713
    | exact resolve eq16713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17131 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16713 (τ X0)
       have i₂ := eq474 X0 X0
       grind)
    | exact superpose eq474 eq16713
    | exact resolve eq16713 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19787 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq224 eq16762
    | exact resolve eq16762 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16762
  have eq19872 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq19787
       have i₂ := eq838 (σ (M.op sF0 y))
       grind)
    | exact superpose eq838 eq19787
    | exact resolve eq19787 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq19787
  have eq20444 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq224 eq16993
    | exact resolve eq16993 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq16993
  have eq20721 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq19872 eq20444
    | exact resolve eq20444 eq19872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19872 eq20444
  have eq30872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1819 eq891
    | exact resolve eq891 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq1819
  have eq30879 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30872
       have r₂ := eq27
       grind)
    | exact resolve eq30872 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30872
  have eq30885 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30879
       have i₂ := eq16598 sF2
       grind)
    | exact superpose eq16598 eq30879
    | exact resolve eq30879 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30879
  have eq30889 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30885
       have i₂ := eq16598 sF3
       grind)
    | exact superpose eq16598 eq30885
    | exact resolve eq30885 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30885
  have eq30893 : x = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30889
       have i₂ := eq16598 x
       grind)
    | exact superpose eq16598 eq30889
    | exact resolve eq30889 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30889
  have eq30895 : (σ x) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30893
       have i₂ := eq16598 y
       grind)
    | exact superpose eq16598 eq30893
    | exact resolve eq30893 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30893
  have eq31049 : (τ (σ x)) = (k y y) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq30895 eq116
    | exact resolve eq116 eq30895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq30895
  have eq31084 : x = (k y y) ∨ x = (k x x) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq30 eq31049
    | exact resolve eq31049 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31049
  have eq31085 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ x = (k y y) := by grind
  clear eq31084
  have eq31103 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq31085 eq142
    | exact resolve eq142 eq31085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq31085
  have eq31145 : x = (k x x) ∨ x = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq31103
    | exact resolve eq31103 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31103
  have eq31146 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq31145
  have eq31185 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16713 y
       have i₂ := eq31146
       grind)
    | exact superpose eq31146 eq16713
    | exact resolve eq16713 eq31146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31188 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq17130 y
       have i₂ := eq31146
       grind)
    | exact superpose eq31146 eq17130
    | exact resolve eq17130 eq31146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31146
  have eq31196 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq31188
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31188
    | exact resolve eq31188 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31188
  have eq31198 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq31185
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31185
    | exact resolve eq31185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31185
  have eq31210 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq31196
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31196
    | exact resolve eq31196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31196
  have eq31219 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq31210
    | exact resolve eq31210 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31210
  have eq31223 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31198 eq31219
    | exact resolve eq31219 eq31198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31219
  have eq31233 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq31223
       grind)
    | exact superpose eq31223 eq40
    | exact resolve eq40 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31245 : (M.op (M.op x y) y) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16713 x
       have i₂ := eq31223
       grind)
    | exact superpose eq31223 eq16713
    | exact resolve eq16713 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31248 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17130 x
       have i₂ := eq31223
       grind)
    | exact superpose eq31223 eq17130
    | exact resolve eq17130 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31249 : (M.op (M.op x y) y) = (M.op (τ x) (τ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17131 x
       have i₂ := eq31223
       grind)
    | exact superpose eq31223 eq17131
    | exact resolve eq17131 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17131
  have eq31262 : (M.op (M.op x y) y) = (k (τ x) (τ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31249
       have i₂ := eq16598 (τ x)
       grind)
    | exact superpose eq16598 eq31249
    | exact resolve eq31249 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31249
  have eq31263 : (M.op (M.op x y) y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31248
       have i₂ := eq16598 (σ x)
       grind)
    | exact superpose eq16598 eq31248
    | exact resolve eq31248 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31248
  have eq31266 : (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31245
       have i₂ := eq16598 x
       grind)
    | exact superpose eq16598 eq31245
    | exact resolve eq31245 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31245
  have eq31274 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31233
    | exact resolve eq31233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31233
  have eq31282 : (M.op (M.op x y) y) = (τ (k x x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31262
       have i₂ := eq474 x x
       grind)
    | exact superpose eq474 eq31262
    | exact resolve eq31262 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq31262
  have eq31283 : (σ (k x x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31263
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq31263
    | exact resolve eq31263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31263
  have eq31286 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31223 eq31266
    | exact resolve eq31266 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31266
  have eq31296 : (M.op (M.op x y) y) = (τ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31223 eq31282
    | exact resolve eq31282 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31223 eq31282
  have eq31297 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31283
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq31283
    | exact resolve eq31283 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31283
  have eq31305 : x = (τ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31286 eq31296
    | exact resolve eq31296 eq31286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31296
  have eq31306 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31297
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31297
    | exact resolve eq31297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31297
  have eq31314 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31274 eq31306
    | exact resolve eq31306 eq31274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31274 eq31306
  have eq31326 : x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x
       have i₂ := eq31305
       grind)
    | exact superpose eq31305 eq14
    | exact resolve eq14 eq31305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31305
  have eq31393 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq31326
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31326
    | exact resolve eq31326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31326
  have eq31897 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31286 eq200
    | exact resolve eq200 eq31286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq31971 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq31286 eq175
    | exact resolve eq175 eq31286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31286
  have eq31976 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31971 x x
       have i₂ := eq186 x x
       grind)
    | (have i₁ := eq31971 x y
       have i₂ := eq186 x x
       grind)
    | exact superpose eq186 eq31971
    | (have j0 := eq31971 x y
       grind)
    | exact resolve eq31971 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31971
  have eq32042 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31393 eq31897
    | exact resolve eq31897 eq31393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31393 eq31897
  have eq32047 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31976
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31976
    | exact resolve eq31976 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31976
  have eq32602 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32042 eq26
    | (have j1 := eq32042 (σ y)
       grind)
    | exact resolve eq26 eq32042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq32042
  have eq32679 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq32602
  have eq32762 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32047 eq31314
    | exact resolve eq31314 eq32047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31314 eq32047
  have eq32769 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq32762
  have eq32774 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32769
       have r₂ := eq32679
       grind)
    | exact resolve eq32769 eq32679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32679 eq32769
  have eq32825 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq32774 eq27
    | exact resolve eq27 eq32774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32826 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq32774 eq183
    | exact resolve eq183 eq32774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq32827 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq32774 eq191
    | exact resolve eq191 eq32774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq32774
  have eq32959 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op x y) (σ y)) y) := by
    intro X0 X1
    first
    | exact superpose eq32827 eq175
    | exact resolve eq175 eq32827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq32963 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq32826 eq32959
    | exact resolve eq32959 eq32826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32826 eq32959
  have eq34535 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32963 X0 X0
       have i₂ := eq16598 X0
       grind)
    | exact superpose eq16598 eq32963
    | exact resolve eq32963 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32963
  have eq34974 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq31198 eq20721
    | exact resolve eq20721 eq31198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20721 eq31198
  have eq34997 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq34974
    | exact resolve eq34974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34974
  have eq35041 : x = (k x x) := by
    first
    | (have r₁ := eq34997
       have r₂ := eq32825
       grind)
    | exact resolve eq34997 eq32825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34997
  have eq35064 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq35041
       grind)
    | exact superpose eq35041 eq40
    | exact resolve eq40 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35077 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq16713 x
       have i₂ := eq35041
       grind)
    | exact superpose eq35041 eq16713
    | exact resolve eq16713 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16713
  have eq35080 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17130 x
       have i₂ := eq35041
       grind)
    | exact superpose eq35041 eq17130
    | exact resolve eq17130 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17130
  have eq35087 : (M.op x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq34535 x
       have i₂ := eq35041
       grind)
    | exact superpose eq35041 eq34535
    | exact resolve eq34535 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34535
  have eq35092 : (k x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq35087
       have i₂ := eq16598 x
       grind)
    | exact superpose eq16598 eq35087
    | exact resolve eq35087 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35087
  have eq35099 : (M.op (M.op x y) y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35080
       have i₂ := eq16598 (σ x)
       grind)
    | exact superpose eq16598 eq35080
    | exact resolve eq35080 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35080
  have eq35102 : (k x x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq35077
       have i₂ := eq16598 x
       grind)
    | exact superpose eq16598 eq35077
    | exact resolve eq35077 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16598 eq35077
  have eq35110 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35064
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35064
    | exact resolve eq35064 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35064
  have eq35114 : x = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq35092
       have i₂ := eq35041
       grind)
    | exact superpose eq35041 eq35092
    | exact resolve eq35092 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35092
  have eq35121 : (σ (k x x)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq35099
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq35099
    | exact resolve eq35099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35099
  have eq35124 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq35102
       have i₂ := eq35041
       grind)
    | exact superpose eq35041 eq35102
    | exact resolve eq35102 eq35041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35041 eq35102
  have eq35135 : (σ (k x x)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq32827 eq35121
    | exact resolve eq35121 eq32827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32827 eq35121
  have eq35147 : x = (σ (k x x)) := by
    first
    | exact superpose eq35114 eq35135
    | exact resolve eq35135 eq35114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35114 eq35135
  have eq35156 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35147
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq35147
    | exact resolve eq35147 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq35147
  have eq35163 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35156
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35156
    | exact resolve eq35156 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35156
  have eq35168 : x = (σ x) := by
    first
    | exact superpose eq35110 eq35163
    | exact resolve eq35163 eq35110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35110 eq35163
  have eq36364 : x = (M.op x y) := by
    first
    | exact superpose eq35124 eq186
    | exact resolve eq186 eq35124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq35124
  have eq36367 : x = (M.op x y) := by
    first
    | (have i₁ := eq36364
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36364
    | exact resolve eq36364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36364
  have eq36527 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq36367
       grind)
    | exact superpose eq36367 eq22
    | exact resolve eq22 eq36367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq36560 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq35168
       have i₂ := eq36367
       grind)
    | exact superpose eq36367 eq35168
    | exact resolve eq35168 eq36367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35168 eq36367
  have eq36582 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36560 eq36527
    | exact resolve eq36527 eq36560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36527 eq36560
  have eq36984 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36582 eq20
    | exact resolve eq20 eq36582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36582
  have eq37144 : False := by grind
  exact eq37144

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_pxy_pyx_Equation4400 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4400 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) x x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 X0 X1 X3
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq186 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq548 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X0) ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X0 X1 X2
       have i₂ := eq16 X0 X1 X0
       grind)
    | exact superpose eq16 eq503
    | (have j0 := eq503 X0 X1 X2
       grind)
    | exact resolve eq503 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq578 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq533 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq533
    | (have j0 := eq533 (σ X0)
       grind)
    | exact resolve eq533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) X3 X4
       have i₂ := eq176 X0 X1 (M.op (M.op X0 X1) X3) X2
       grind)
    | (have i₁ := eq16 (M.op X0 X1) X3 X4
       have i₂ := eq176 X0 X1 X2 (M.op (M.op X0 X1) X3)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) x
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X0 X1)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq778 X0 X1 X2 x X4
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq778
    | exact resolve eq778 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq1087 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq905 X0 X1
       grind)
    | exact superpose eq905 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq905 X0 X1
       grind)
    | exact resolve eq13 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1114 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1087 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1154 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 (M.op X0 X1) x
       have i₂ := eq16 X0 X1 (M.op (M.op X0 X1) x)
       grind)
    | exact superpose eq16 eq1114
    | exact resolve eq1114 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1962 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq505
       grind)
    | exact superpose eq505 eq39
    | exact resolve eq39 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq505
  have eq1963 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1962
    | exact resolve eq1962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1962
  have eq1965 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1963
    | exact resolve eq1963 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq3920 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X3 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 (M.op X0 X1)) X3
       have i₂ := eq972 X0 X1 X2 X3
       grind)
    | exact superpose eq972 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X1)) X3
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) x)
       have r₂ := eq972 X0 X1 (M.op (M.op X0 (M.op X0 X1)) x) x
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X1)) (M.op (M.op X0 X1) X2)
       have r₂ := eq972 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact resolve eq13 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq10427 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (k (M.op (M.op x y) X1) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq186 eq1154
    | exact resolve eq1154 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq10746 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (k (M.op X0 (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq548 (M.op X0 X1) x x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq548
    | (have j0 := eq548 (M.op X0 X1) X1 x
       grind)
    | exact resolve eq548 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq10913 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10746 X0 X1 x
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq10746
    | (have j0 := eq10746 X0 X1 x
       grind)
    | exact resolve eq10746 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq10746
  have eq10963 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10913 X0 X1
       have j1 := eq3920 X0 X1 x (M.op X0 X1)
       grind)
    | (have r₁ := eq10913 (M.op X0 X1) X1
       have r₂ := eq3920 X0 X1 (M.op (M.op X0 X1) X1) (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1))
       grind)
    | (have r₁ := eq10913 (M.op X0 X1) x
       have r₂ := eq3920 X0 X1 x (M.op (M.op (M.op X0 X1) x) (M.op (M.op X0 X1) (M.op (M.op X0 X1) x)))
       grind)
    | (have r₁ := eq10913 X0 X1
       have r₂ := eq3920 X0 X1 (M.op X0 (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact resolve eq10913 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10913
  have eq10990 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10963 X0 X1
       have j1 := eq3920 X0 X1 x (M.op X0 X1)
       grind)
    | (have r₁ := eq10963 (M.op X0 X1) X1
       have r₂ := eq3920 X0 X1 (M.op (M.op X0 X1) X1) (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X1) X1))
       grind)
    | (have r₁ := eq10963 (M.op X0 X1) x
       have r₂ := eq3920 X0 X1 x (M.op (M.op (M.op X0 X1) x) (M.op (M.op X0 X1) x))
       grind)
    | (have r₁ := eq10963 X0 X1
       have r₂ := eq3920 X0 X1 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq10963 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920 eq10963
  have eq22908 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) ≠ (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq10427 eq578
    | (have j0 := eq578 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq578 eq10427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq10427
  have eq22946 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have j0 := eq22908 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22908
  have eq23348 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op x y) X0)) X1) = (M.op (σ (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq22946 eq176
    | exact resolve eq176 eq22946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23477 : ∀ X0 X1 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq23348 eq22946
    | exact resolve eq22946 eq23348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22946 eq23348
  have eq23542 : ∀ X1 : G, (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) X1) := by
    intro X1
    first
    | exact superpose eq180 eq23477
    | exact resolve eq23477 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq23477
  have eq25278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1965 eq525
    | exact resolve eq525 eq1965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq1965
  have eq25287 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq25278
       have r₂ := eq27
       grind)
    | exact resolve eq25278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25278
  have eq25318 : (σ x) = (k (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25287 eq1154
    | exact resolve eq1154 eq25287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq25327 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25287 eq25318
    | exact resolve eq25318 eq25287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25287 eq25318
  have eq25348 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq25327
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq25327
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq25327
       have r₂ := eq13 y x
       grind)
    | exact resolve eq25327 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25327
  have eq25363 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25348 eq141
    | exact resolve eq141 eq25348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq25348
  have eq25372 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq25363
    | exact resolve eq25363 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25363
  have eq25377 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq25372
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq25372
       have r₂ := eq13 y x
       grind)
    | exact resolve eq25372 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25372
  have eq25386 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq533 x
       have i₂ := eq25377
       grind)
    | exact superpose eq25377 eq533
    | (have j0 := eq533 x
       grind)
    | (have r₁ := eq533 x
       have r₂ := eq25377
       grind)
    | exact resolve eq533 eq25377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25377
  have eq25389 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq25386
  have eq25703 : (M.op y x) = (k (M.op y x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10990 y x
       have i₂ := eq25389
       grind)
    | exact superpose eq25389 eq10990
    | exact resolve eq10990 eq25389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10990
  have eq25705 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25389 eq25703
    | exact resolve eq25703 eq25389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25389 eq25703
  have eq25727 : x = (k x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq25705
       have r₂ := eq13 x x
       grind)
    | exact resolve eq25705 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25705
  have eq25744 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq533 x
       have i₂ := eq25727
       grind)
    | exact superpose eq25727 eq533
    | (have j0 := eq533 x
       grind)
    | (have r₁ := eq533 x
       have r₂ := eq25727
       grind)
    | exact resolve eq533 eq25727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq25727
  have eq25747 : x = (M.op x x) := by grind
  clear eq25744
  have eq25760 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x x x x
       have i₂ := eq25747
       grind)
    | exact superpose eq25747 eq176
    | exact resolve eq176 eq25747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq25988 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq25747
       have i₂ := eq25760 x X0
       grind)
    | (have i₁ := eq25747
       have i₂ := eq25760 X0 x
       grind)
    | exact superpose eq25760 eq25747
    | exact resolve eq25747 eq25760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25747
  have eq25989 : ∀ X0 : G, (M.op x y) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq25760 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq25760 X0 y
       grind)
    | exact superpose eq25760 eq18
    | (have j1 := eq25760 y X0
       grind)
    | exact resolve eq18 eq25760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25760
  have eq26064 : x = (M.op x y) := by
    first
    | (have i₁ := eq25988 x
       have i₂ := eq25989 x
       grind)
    | (have i₁ := eq25988 y
       have i₂ := eq25989 x
       grind)
    | exact superpose eq25989 eq25988
    | (have j0 := eq25988 y
       grind)
    | exact resolve eq25988 eq25989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25988
  have eq26095 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq26064
       grind)
    | exact superpose eq26064 eq22
    | exact resolve eq22 eq26064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26064
  have eq26178 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26095 eq20
    | exact resolve eq20 eq26095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26095
  have eq26806 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq23542 x
       have i₂ := eq25989 sF0
       grind)
    | exact superpose eq25989 eq23542
    | exact resolve eq23542 eq25989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23542 eq25989
  have eq26872 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq26806
    | (have j0 := eq26806 X0
       grind)
    | exact resolve eq26806 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26806
  have eq26889 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq26178 eq26872
    | exact resolve eq26872 eq26178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26872
  have eq27208 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26889 eq26
    | (have j1 := eq26889 (σ y)
       grind)
    | exact resolve eq26 eq26889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq26889
  have eq27298 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq27208 eq27
    | exact resolve eq27 eq27208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq27208
  have eq27320 : False := by grind
  exact eq27320

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pxx_x_pyx_Equation4401 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
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
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X0 x X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) x) := by
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
  have eq56 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 X2)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op X0 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : y ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
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
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X2) X0) = X0 ∨ (M.op X0 X2) = (k (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) X0
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 X2) X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq105 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq105
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq217 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq55 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ y)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq217 eq220
    | exact resolve eq220 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq378 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq230 eq233
    | exact resolve eq233 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq923 : ∀ X1 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x X1) x) ∨ (M.op x x) = (k x (M.op (M.op x y) x)) := by
    intro X1
    first
    | (have i₁ := eq67 x X1 (M.op x x)
       have i₂ := eq55 x
       grind)
    | exact superpose eq55 eq67
    | (have r₁ := eq67 x y (M.op x x)
       have r₂ := eq55 x
       grind)
    | exact resolve eq67 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) ≠ (M.op (M.op (σ x) X1) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X1
    first
    | exact superpose eq56 eq67
    | (have r₁ := eq67 (σ x) (σ y) (M.op (σ x) x)
       have r₂ := eq56 x
       grind)
    | exact resolve eq67 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq953 : (M.op (M.op (σ x) (σ y)) (σ x)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq378 eq924
    | exact resolve eq924 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq954 : (M.op (M.op x y) x) ≠ (M.op x (M.op x y)) ∨ (M.op x x) = (k x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq923 x
       have i₂ := eq373 x
       grind)
    | exact superpose eq373 eq923
    | exact resolve eq923 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq957 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have r₁ := eq953
       have r₂ := eq230
       grind)
    | exact resolve eq953 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq958 : (M.op x x) = (k x (M.op (M.op x y) x)) := by
    first
    | (have r₁ := eq954
       have r₂ := eq217
       grind)
    | exact resolve eq954 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq959 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq230 eq957
    | exact resolve eq957 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq960 : (M.op x x) = (k x (M.op x (M.op x y))) := by
    first
    | exact superpose eq217 eq958
    | exact resolve eq958 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1581 : ∀ X1 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x X1) x) ∨ x = (M.op (M.op (M.op x y) x) x) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) x) := by
    intro X1
    first
    | (have i₁ := eq80 x X1 (M.op x x)
       have i₂ := eq55 x
       grind)
    | exact superpose eq55 eq80
    | (have r₁ := eq80 x y (M.op x x)
       have r₂ := eq55 x
       grind)
    | exact resolve eq80 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1583 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) ≠ (M.op (M.op (σ x) X1) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    intro X1
    first
    | exact superpose eq56 eq80
    | (have r₁ := eq80 (σ x) (σ y) (M.op (σ x) x)
       have r₂ := eq56 x
       grind)
    | exact resolve eq80 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq80
  have eq1635 : (M.op (M.op (σ x) (σ y)) (σ x)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq378 eq1583
    | exact resolve eq1583 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1637 : (M.op (M.op x y) x) ≠ (M.op x (M.op x y)) ∨ x = (M.op (M.op (M.op x y) x) x) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq1581 x
       have i₂ := eq373 x
       grind)
    | exact superpose eq373 eq1581
    | exact resolve eq1581 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1643 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | (have r₁ := eq1635
       have r₂ := eq230
       grind)
    | exact resolve eq1635 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1644 : x = (M.op (M.op (M.op x y) x) x) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) x) := by
    first
    | (have r₁ := eq1637
       have r₂ := eq217
       grind)
    | exact resolve eq1637 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1645 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq230 eq1643
    | exact resolve eq1643 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1646 : x = (M.op (M.op x (M.op x y)) x) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq217 eq1644
    | exact resolve eq1644 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1647 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq378 eq1645
    | exact resolve eq1645 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq1645
  have eq1648 : x = (M.op x (M.op x y)) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq1646
       have i₂ := eq373 sF0
       grind)
    | exact superpose eq373 eq1646
    | exact resolve eq1646 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1649 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq230 eq1647
    | exact resolve eq1647 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq1647
  have eq1650 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq217 eq1648
    | exact resolve eq1648 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1765 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq99 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1766 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1767 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1766 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq7429 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1767 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1767
    | (have j0 := eq1767 (τ X0)
       grind)
    | exact resolve eq1767 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1767
  have eq7437 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7429 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7429
    | (have j0 := eq7429 X0
       grind)
    | exact resolve eq7429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7429
  have eq7443 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7437 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7437
    | (have j0 := eq7437 X0
       grind)
    | exact resolve eq7437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7437
  have eq13876 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq13909 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq13876
    | exact resolve eq13876 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13876
  have eq13912 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq13909
       have r₂ := eq13 x x
       grind)
    | exact resolve eq13909 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq13913 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq13912
       grind)
    | exact superpose eq13912 eq43
    | exact resolve eq43 eq13912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq15185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq121 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15185
    | exact resolve eq15185 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15185
  have eq15197 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq15186
       have r₂ := eq27
       grind)
    | exact resolve eq15186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15186
  have eq15199 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15197
    | exact resolve eq15197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15197
  have eq15201 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15199 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15199
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15199
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15199
       grind)
    | exact resolve eq12 eq15199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15199
  have eq15245 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq15201
  have eq15280 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15245
    | exact resolve eq15245 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15245
  have eq15281 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq15280
  have eq15289 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15281 eq61
    | exact resolve eq61 eq15281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15281
  have eq15305 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq15289
    | exact resolve eq15289 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15289
  have eq15922 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15305
       grind)
    | exact superpose eq15305 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15305
  have eq15923 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15922
  have eq15925 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15923
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15923
    | exact resolve eq15923 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15923
  have eq15926 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15925
  have eq15936 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15926
       grind)
    | exact superpose eq15926 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15926
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15926
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15926
       grind)
    | exact resolve eq12 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15938 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq15926
       grind)
    | exact superpose eq15926 eq14
    | exact resolve eq14 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15983 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15936
  have eq16018 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15938 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15938
    | (have j0 := eq15938 X0
       grind)
    | exact resolve eq15938 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15938
  have eq16019 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15983
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15983
    | exact resolve eq15983 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15983
  have eq16020 : x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16019
  have eq16026 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq16020
       grind)
    | exact superpose eq16020 eq44
    | exact resolve eq44 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16020
  have eq16042 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16026
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16026
    | exact resolve eq16026 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026
  have eq16053 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16042 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq16042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16042
  have eq16054 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16053
  have eq16056 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16054
    | exact resolve eq16054 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16054
  have eq16057 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16056
  have eq16073 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16057 eq14
    | exact resolve eq14 eq16057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16153 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq16073
    | (have j0 := eq16073 X0
       grind)
    | exact resolve eq16073 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16073
  have eq17515 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16018 x
       have i₂ := eq15926
       grind)
    | exact superpose eq15926 eq16018
    | exact resolve eq16018 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16018
  have eq17640 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17515
  have eq17797 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15926
       have i₂ := eq17640
       grind)
    | exact superpose eq17640 eq15926
    | exact resolve eq15926 eq17640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15926 eq17640
  have eq17854 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17797
  have eq18942 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16057 eq16153
    | exact resolve eq16153 eq16057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16153
  have eq19073 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18942
  have eq19921 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19073 eq16057
    | exact resolve eq16057 eq19073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16057 eq19073
  have eq19986 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19921
  have eq20001 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19986 eq27
    | exact resolve eq27 eq19986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20002 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19986 eq70
    | (have r₁ := eq70
       have r₂ := eq19986
       grind)
    | exact resolve eq70 eq19986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq20013 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19986 eq1649
    | exact resolve eq1649 eq19986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq20016 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq20018 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20002
  have eq20021 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20013
    | exact resolve eq20013 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20013
  have eq20031 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20021
    | exact resolve eq20021 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20021
  have eq20032 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20031
  have eq20115 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19986 eq20032
    | exact resolve eq20032 eq19986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19986 eq20032
  have eq20122 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20115
  have eq20125 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20122
       have r₂ := eq20016
       grind)
    | exact resolve eq20122 eq20016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20016 eq20122
  have eq20132 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20125 eq88
    | exact resolve eq88 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq20133 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20125 eq121
    | exact resolve eq121 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq20125
  have eq20146 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20133
  have eq20158 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20146
       have r₂ := eq20001
       grind)
    | exact resolve eq20146 eq20001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20001 eq20146
  have eq20159 : y = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq20132
    | exact resolve eq20132 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20132
  have eq20170 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq20158
       grind)
    | exact superpose eq20158 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20158
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20158
       grind)
    | exact resolve eq12 eq20158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20171 : x ≠ x ∨ (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20158
       grind)
    | exact superpose eq20158 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20158
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20158
       grind)
    | exact resolve eq13 eq20158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20176 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq52 y X0 x
       have i₂ := eq20158
       grind)
    | exact superpose eq20158 eq52
    | exact resolve eq52 eq20158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq20158
  have eq20228 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20171
  have eq20229 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20170
  have eq20265 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20176 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20176
    | (have j0 := eq20176 X0
       grind)
    | exact resolve eq20176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20176
  have eq20270 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20229
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20229
    | exact resolve eq20229 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20229
  have eq20271 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20270
  have eq20304 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20271
       grind)
    | exact superpose eq20271 eq44
    | exact resolve eq44 eq20271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20271
  have eq20320 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20304
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20304
    | exact resolve eq20304 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20304
  have eq20580 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20018 eq20320
    | exact resolve eq20320 eq20018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20018 eq20320
  have eq20582 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20580
  have eq21377 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20159
       have i₂ := eq20228
       grind)
    | exact superpose eq20228 eq20159
    | exact resolve eq20159 eq20228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20159 eq20228
  have eq21379 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21377
  have eq21832 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20265 y
       have i₂ := eq21379
       grind)
    | exact superpose eq21379 eq20265
    | exact resolve eq20265 eq21379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20265
  have eq21974 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21832
  have eq22000 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21379
       have i₂ := eq21974
       grind)
    | exact superpose eq21974 eq21379
    | exact resolve eq21379 eq21974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21379 eq21974
  have eq22069 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22000
  have eq22094 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22069 eq27
    | exact resolve eq27 eq22069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22102 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22069 eq959
    | exact resolve eq959 eq22069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq22110 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22069 eq17854
    | exact resolve eq17854 eq22069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22119 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22110
  have eq22125 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22119 eq26
    | exact resolve eq26 eq22119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22126 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22119 eq29
    | exact resolve eq29 eq22119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22131 : (k x y) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22119 eq61
    | exact resolve eq61 eq22119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq22119
  have eq22286 : (k x x) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49 eq22131
    | exact resolve eq22131 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22131
  have eq22291 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq22126
    | exact resolve eq22126 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22126
  have eq22318 : (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22286
       have i₂ := eq13912
       grind)
    | exact superpose eq13912 eq22286
    | exact resolve eq22286 eq13912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22286
  have eq22330 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22318
       have r₂ := eq69
       grind)
    | exact resolve eq22318 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq22318
  have eq23017 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22291 eq20
    | exact resolve eq20 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23076 : (M.op x x) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22291 eq960
    | exact resolve eq960 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq23080 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22291 eq1650
    | exact resolve eq1650 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq23096 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23080
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23080
    | exact resolve eq23080 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23080
  have eq23100 : (k x (M.op x y)) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23076
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23076
    | exact resolve eq23076 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23076
  have eq23157 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23017
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23017
    | exact resolve eq23017 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23017
  have eq23158 : x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23096
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23096
    | exact resolve eq23096 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23096
  have eq23159 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq23158
  have eq24033 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq22330
       grind)
    | exact superpose eq22330 eq44
    | exact resolve eq44 eq22330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq22330
  have eq24051 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24033
       have i₂ := eq13913
       grind)
    | exact superpose eq13913 eq24033
    | exact resolve eq24033 eq13913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24033
  have eq24966 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22125 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq22125
       grind)
    | exact resolve eq13 eq22125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25095 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24966
       have r₂ := eq22069
       grind)
    | exact resolve eq24966 eq22069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22069 eq24966
  have eq25960 : y = (k y x) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22291 eq23159
    | exact resolve eq23159 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23159
  have eq25972 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq25960
  have eq25995 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25095 eq7443
    | (have j0 := eq7443 (σ x)
       grind)
    | exact resolve eq7443 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7443 eq25095
  have eq26002 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25995
       have r₂ := eq20582
       grind)
    | exact resolve eq25995 eq20582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20582 eq25995
  have eq26225 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26002 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq26002
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26002
       grind)
    | exact resolve eq13 eq26002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26002
  have eq26293 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26225
  have eq27173 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26293 eq49
    | exact resolve eq49 eq26293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26293
  have eq27198 : (τ (σ x)) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27173
       have i₂ := eq13912
       grind)
    | exact superpose eq13912 eq27173
    | exact resolve eq27173 eq13912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27173
  have eq27207 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq27198
    | exact resolve eq27198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27198
  have eq27220 : (M.op x x) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq373 x
       have i₂ := eq27207
       grind)
    | exact superpose eq27207 eq373
    | exact resolve eq373 eq27207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27207
  have eq27342 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22125 eq22102
    | exact resolve eq22102 eq22125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22102 eq22125
  have eq27347 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq27342
  have eq27361 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17854 eq27347
    | exact resolve eq27347 eq17854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17854 eq27347
  have eq27372 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq27361
  have eq27404 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27372 eq24051
    | exact resolve eq24051 eq27372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24051 eq27372
  have eq27406 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq27404
  have eq27439 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27406 eq49
    | exact resolve eq49 eq27406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq27406
  have eq27467 : (τ (σ y)) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27439
       have i₂ := eq13912
       grind)
    | exact superpose eq13912 eq27439
    | exact resolve eq27439 eq13912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13912 eq27439
  have eq27476 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq27467
    | exact resolve eq27467 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27467
  have eq28524 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq27476
       grind)
    | exact superpose eq27476 eq55
    | exact resolve eq55 eq27476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq28669 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq217 eq28524
    | exact resolve eq28524 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq28524
  have eq28720 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28669
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28669
    | exact resolve eq28669 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28669
  have eq44454 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27220 eq28720
    | exact resolve eq28720 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27220 eq28720
  have eq44557 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44454
  have eq44581 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27476
       have i₂ := eq44557
       grind)
    | exact superpose eq44557 eq27476
    | exact resolve eq27476 eq44557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27476 eq44557
  have eq44681 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq44581
  have eq44918 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq44681
  have eq54454 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1765 x y
       have i₂ := eq25972
       grind)
    | exact superpose eq25972 eq1765
    | (have j0 := eq1765 x y
       grind)
    | exact resolve eq1765 eq25972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765 eq25972
  have eq54701 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq54454
  have eq54842 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq54701
       have r₂ := eq44918
       grind)
    | exact resolve eq54701 eq44918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54701
  have eq54984 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54842
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54842
    | exact resolve eq54842 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54842
  have eq55116 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54984
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54984
    | exact resolve eq54984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54984
  have eq55241 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq55116
    | exact resolve eq55116 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55116
  have eq55359 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55241
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55241
    | exact resolve eq55241 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55241
  have eq55390 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq55359
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55359
    | exact resolve eq55359 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55359
  have eq56103 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55390 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq55390
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq55390
       grind)
    | exact resolve eq12 eq55390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55390
  have eq56212 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56103
  have eq56302 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq56212
    | exact resolve eq56212 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56212
  have eq56303 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56302
  have eq127301 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23157 eq56303
    | exact resolve eq56303 eq23157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23157 eq56303
  have eq127344 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq127301
  have eq127357 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127344
       have r₂ := eq44918
       grind)
    | exact resolve eq127344 eq44918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127344
  have eq127361 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127357
       have r₂ := eq27
       grind)
    | exact resolve eq127357 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127357
  have eq127366 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127361 eq65
    | exact resolve eq65 eq127361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq127361
  have eq127390 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq127366
    | exact resolve eq127366 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq127366
  have eq128271 : x = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127390 eq23100
    | exact resolve eq23100 eq127390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23100 eq127390
  have eq128287 : x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq128271
  have eq128301 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq128287
       have r₂ := eq44918
       grind)
    | exact resolve eq128287 eq44918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128287
  have eq128387 : (M.op x x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq373 x
       have i₂ := eq128301
       grind)
    | exact superpose eq128301 eq373
    | exact resolve eq373 eq128301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq133827 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq22291 eq128387
    | exact resolve eq128387 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22291 eq128387
  have eq134043 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq133827
  have eq134051 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq134043
       have r₂ := eq44918
       grind)
    | exact resolve eq134043 eq44918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44918 eq134043
  have eq134053 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134051
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq134051
    | exact resolve eq134051 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134051
  have eq134072 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128301
       have i₂ := eq134053
       grind)
    | exact superpose eq134053 eq128301
    | exact resolve eq128301 eq134053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128301 eq134053
  have eq134270 : x = (M.op x y) := by grind
  clear eq134072
  have eq134575 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq134270 eq20
    | exact resolve eq20 eq134270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq134705 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq134575
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq134575
    | exact resolve eq134575 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134575
  have eq134706 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq134705 eq26
    | exact resolve eq26 eq134705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq134798 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134705 eq22094
    | (have r₁ := eq22094
       have r₂ := eq134705
       grind)
    | exact resolve eq22094 eq134705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22094
  have eq134845 : y = (M.op x y) := by grind
  clear eq134798
  have eq134850 : x = y := by
    first
    | exact superpose eq134270 eq134845
    | exact resolve eq134845 eq134270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134845
  have eq137175 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq134850
       grind)
    | exact superpose eq134850 eq18
    | exact resolve eq18 eq134850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq137176 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq134850
       grind)
    | exact superpose eq134850 eq24
    | exact resolve eq24 eq134850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq134850
  have eq137360 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq137176
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137176
    | exact resolve eq137176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137176
  have eq137361 : x = (M.op x x) := by
    first
    | exact superpose eq134270 eq137175
    | exact resolve eq137175 eq134270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134270 eq137175
  have eq137422 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134705 eq137360
    | exact resolve eq137360 eq134705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137360
  have eq137755 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq137422 eq134706
    | exact resolve eq134706 eq137422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134706 eq137422
  have eq140367 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13913
       have i₂ := eq137361
       grind)
    | exact superpose eq137361 eq13913
    | exact resolve eq13913 eq137361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13913 eq137361
  have eq140664 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134705 eq140367
    | exact resolve eq140367 eq134705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140367
  have eq140729 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq140664
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140664
    | exact resolve eq140664 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq140664
  have eq140784 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134705 eq140729
    | exact resolve eq140729 eq134705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134705 eq140729
  have eq143257 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq140784 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq140784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140784
  have eq143266 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq143257
  have eq143271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq137755 eq143266
    | exact resolve eq143266 eq137755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137755 eq143266
  have eq143282 : False := by grind
  exact eq143282

/-- `Equation4404`: `x ◇ (x ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_pxy_pyx_Equation4404 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4404 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4404.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq176 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X4) X5) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X4 X5
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X0 X2) X4) X5) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X2) x X4 X5
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X0 x X4 X5
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X0 X2 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X4 X1 (M.op (M.op X0 X1) x)
       have i₂ := eq16 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X2 : G, (M.op (M.op x y) X2) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq182 (M.op x x) X2
       have i₂ := eq182 x X0
       grind)
    | exact superpose eq182 eq182
    | exact resolve eq182 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq182 x X2
       have i₂ := eq182 x X0
       grind)
    | exact superpose eq182 eq182
    | exact resolve eq182 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op x X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq182 x X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq191 eq16
    | exact resolve eq16 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq183
    | (have j0 := eq183 (σ y) X0
       grind)
    | exact resolve eq183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X2
    first
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X2
    first
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X2) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq257 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq237 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq237 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (M.op (M.op x y) X1) ≠ (M.op (M.op x y) X0) ∨ x = (k x (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq189 eq13
    | (have j0 := eq13 x (M.op (M.op x y) X1)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x (M.op (M.op x y) X0))
       have r₂ := eq189 X0 (M.op x (M.op (M.op x y) X0))
       grind)
    | (have r₁ := eq13 x (M.op (M.op x y) x)
       have r₂ := eq189 x x
       grind)
    | exact resolve eq13 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq316 : ∀ X1 : G, x = (k x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | (have j0 := eq315 x X1
       grind)
    | (have r₁ := eq315 x x
       have r₂ := eq191 x x
       grind)
    | (have r₁ := eq315 x x
       have r₂ := eq191 x x
       grind)
    | exact resolve eq315 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq329 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq316 eq35
    | exact resolve eq35 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq316
  have eq330 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq329 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq329
    | (have j0 := eq329 X0
       grind)
    | exact resolve eq329 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq367 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq195 eq188
    | exact resolve eq188 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq410 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq238 eq13
    | (have j0 := eq13 (σ x) (M.op (M.op (σ x) (σ y)) X1)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))
       have r₂ := eq238 X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (M.op (σ x) (σ y)) x)
       have r₂ := eq238 x x
       grind)
    | exact resolve eq13 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq411 : ∀ X1 : G, (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | (have j0 := eq410 x X1
       grind)
    | (have r₁ := eq410 x x
       have r₂ := eq240 x x
       grind)
    | (have r₁ := eq410 x x
       have r₂ := eq240 x x
       grind)
    | exact resolve eq410 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq422 : (σ x) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq237 eq411
    | exact resolve eq411 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq441 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq244 eq237
    | exact resolve eq237 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq475 : (τ (σ x)) = (k x (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq422 eq90
    | exact resolve eq90 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq422
  have eq486 : x = (k x (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq29 eq475
    | exact resolve eq475 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq720 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op x (k X0 x)) ∨ x = (M.op x x) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 X1
       have i₂ := eq11 X0 x
       grind)
    | exact superpose eq11 eq182
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1085 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq758 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq758
    | (have j0 := eq758 (σ X0)
       grind)
    | exact resolve eq758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have j0 := eq257 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq2699 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X3) X4) ∨ (k X0 (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X3) X4)
       have i₂ := eq176 X0 X3 X4 X1 X2
       grind)
    | exact superpose eq176 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X3) X4)
       grind)
    | (have r₁ := eq13 (M.op X0 X4) (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq176 X0 X1 X2 X4 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X4) x)
       have r₂ := eq176 X0 X4 x X4 x
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2823 : ∀ X0 X3 X4 : G, (k X0 (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X3 X4
    first
    | (have j0 := eq2699 X0 x x X3 X4
       grind)
    | (have r₁ := eq2699 X0 x x X4 x
       have r₂ := eq178 X0 x x X4 x
       grind)
    | (have r₁ := eq2699 X0 X4 x x x
       have r₂ := eq178 X0 x x X4 x
       grind)
    | exact resolve eq2699 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq2699
  have eq3078 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) = (M.op X0 (M.op X0 X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq185 X0 X1 X2 (M.op (M.op (M.op X0 X1) X2) x) X6
       have i₂ := eq185 (M.op (M.op X0 X1) X2) X3 X4 X5 x
       grind)
    | exact superpose eq185 eq185
    | exact resolve eq185 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq3460 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2823 X0 x x
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq2823
    | exact resolve eq2823 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823
  have eq3589 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (k (M.op (M.op x y) X1) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq236 eq3460
    | exact resolve eq3460 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq3628 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op sF3 (M.op sF3 x))
       have i₂ := eq3460 sF3 x
       grind)
    | exact superpose eq3460 eq107
    | exact resolve eq107 eq3460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3460
  have eq3629 : ∀ X0 : G, y = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq31 eq3628
    | exact resolve eq3628 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3628
  have eq5082 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq724
       grind)
    | exact superpose eq724 eq39
    | exact resolve eq39 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5083 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq5082
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5082
    | exact resolve eq5082 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5082
  have eq5085 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq5083
    | exact resolve eq5083 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5083
  have eq32844 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) ≠ (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq3589 eq1085
    | (have j0 := eq1085 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq1085 eq3589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq32886 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have j0 := eq32844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32844
  have eq40511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5085 eq746
    | exact resolve eq746 eq5085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq40521 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq40511
       have r₂ := eq27
       grind)
    | exact resolve eq40511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40511
  have eq40532 : y = (k y (τ (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq40521 eq3629
    | exact resolve eq3629 eq40521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629
  have eq40605 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq40521 eq40532
    | exact resolve eq40532 eq40521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40521 eq40532
  have eq40615 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq40605
    | exact resolve eq40605 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40605
  have eq40617 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq40615
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq40615
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq40615
       have r₂ := eq13 y x
       grind)
    | exact resolve eq40615 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40615
  have eq40632 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40617 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq40617
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq40617
       grind)
    | exact resolve eq13 eq40617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40617
  have eq40675 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq40632
  have eq40707 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40675 eq141
    | exact resolve eq141 eq40675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq40675
  have eq40716 : x = (k x x) ∨ y = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq40707
    | exact resolve eq40707 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40707
  have eq40721 : y = (k y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq40716
       have r₂ := eq13 x x
       grind)
    | exact resolve eq40716 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40716
  have eq40727 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq724
       have i₂ := eq40721
       grind)
    | exact superpose eq40721 eq724
    | exact resolve eq724 eq40721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq40729 : (σ y) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq40721
       grind)
    | exact superpose eq40721 eq39
    | exact resolve eq39 eq40721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq40735 : (σ y) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq40729
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40729
    | exact resolve eq40729 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40729
  have eq40737 : x = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq758 x
       grind)
    | (have r₁ := eq40727
       have r₂ := eq758 x
       grind)
    | exact resolve eq40727 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40727
  have eq40746 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (k x x) := by
    first
    | exact superpose eq40735 eq5085
    | exact resolve eq5085 eq40735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5085 eq40735
  have eq40762 : x = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq758 x
       grind)
    | (have r₁ := eq40746
       have r₂ := eq758 x
       grind)
    | exact resolve eq40746 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40746
  have eq40781 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op x (M.op y (M.op y X2))) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 y X1 x x x
       have i₂ := eq40737
       grind)
    | exact superpose eq40737 eq177
    | exact resolve eq177 eq40737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40787 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq184 y X0 x
       have i₂ := eq40737
       grind)
    | exact superpose eq40737 eq184
    | exact resolve eq184 eq40737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40840 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40737 eq40787
    | exact resolve eq40787 eq40737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40737 eq40787
  have eq40843 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op x (M.op y (M.op y X2))) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq40781 x x X2
       have i₂ := eq367 x x
       grind)
    | exact superpose eq367 eq40781
    | exact resolve eq40781 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40781
  have eq40853 : (M.op x (M.op x y)) = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40840 eq40843
    | exact resolve eq40843 eq40840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40843
  have eq40888 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op x (M.op y (M.op y X2))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 y X1 x x x
       have i₂ := eq40762
       grind)
    | exact superpose eq40762 eq177
    | exact resolve eq177 eq40762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq40894 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq184 y X0 x
       have i₂ := eq40762
       grind)
    | exact superpose eq40762 eq184
    | exact resolve eq184 eq40762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40947 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq40762 eq40894
    | exact resolve eq40894 eq40762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40762 eq40894
  have eq40950 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op x (M.op y (M.op y X2))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have i₁ := eq40888 x x X2
       have i₂ := eq367 x x
       grind)
    | exact superpose eq367 eq40888
    | exact resolve eq40888 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40888
  have eq40958 : (M.op x (M.op x y)) = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40947 eq40950
    | exact resolve eq40950 eq40947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40950
  have eq41940 : ∀ X1 X2 : G, x = (M.op (M.op y X1) X2) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 y x X1 X2
       have i₂ := eq40840 x
       grind)
    | exact superpose eq40840 eq16
    | exact resolve eq16 eq40840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42135 : x ≠ (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq40853
  have eq42466 : ∀ X1 X2 : G, x = (M.op (M.op y X1) X2) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 y x X1 X2
       have i₂ := eq40947 x
       grind)
    | exact superpose eq40947 eq16
    | exact resolve eq16 eq40947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42664 : x ≠ (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq40958
  have eq45012 : ∀ X0 X1 X2 X3 X4 : G, x = (M.op (M.op (M.op (M.op (M.op y X0) X1) X2) X3) X4) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40947 x
       have i₂ := eq3078 y X0 X1 X2 X3 X4 x
       grind)
    | exact superpose eq3078 eq40947
    | exact resolve eq40947 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40947
  have eq45013 : ∀ X0 X1 X2 X3 X4 : G, x = (M.op (M.op (M.op (M.op (M.op y X0) X1) X2) X3) X4) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40840 x
       have i₂ := eq3078 y X0 X1 X2 X3 X4 x
       grind)
    | exact superpose eq3078 eq40840
    | exact resolve eq40840 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078 eq40840
  have eq45181 : ∀ X2 X3 X4 : G, x = (M.op (M.op (M.op x X2) X3) X4) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X2 X3 X4
    first
    | exact superpose eq41940 eq45013
    | exact resolve eq45013 eq41940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41940 eq45013
  have eq45182 : ∀ X2 X3 X4 : G, x = (M.op (M.op (M.op x X2) X3) X4) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2 X3 X4
    first
    | exact superpose eq42466 eq45012
    | exact resolve eq45012 eq42466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42466 eq45012
  have eq45392 : ∀ X4 : G, x = (M.op (M.op x (M.op x y)) X4) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X4
    first
    | (have i₁ := eq45181 x x X4
       have i₂ := eq367 x x
       grind)
    | exact superpose eq367 eq45181
    | exact resolve eq45181 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45181
  have eq45393 : ∀ X4 : G, x = (M.op (M.op x (M.op x y)) X4) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X4
    first
    | (have i₁ := eq45182 x x X4
       have i₂ := eq367 x x
       grind)
    | exact superpose eq367 eq45182
    | exact resolve eq45182 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45182
  have eq45567 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45392 x
       have i₂ := eq367 sF0 x
       grind)
    | exact superpose eq367 eq45392
    | exact resolve eq45392 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45392
  have eq45568 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45393 x
       have i₂ := eq367 sF0 x
       grind)
    | exact superpose eq367 eq45393
    | exact resolve eq45393 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45393
  have eq45717 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq45567
       have r₂ := eq42135
       grind)
    | exact resolve eq45567 eq42135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42135 eq45567
  have eq45718 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq45568
       have r₂ := eq42664
       grind)
    | exact resolve eq45568 eq42664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42664 eq45568
  have eq45828 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 x X1
       have i₂ := eq45717
       grind)
    | exact superpose eq45717 eq195
    | exact resolve eq195 eq45717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq45940 : x ≠ x ∨ x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq45718
       grind)
    | exact superpose eq45718 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq45718
       grind)
    | exact resolve eq13 eq45718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45718
  have eq45988 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq45940
  have eq46032 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1085 x
       have i₂ := eq45988
       grind)
    | exact superpose eq45988 eq1085
    | (have j0 := eq1085 x
       grind)
    | exact resolve eq1085 eq45988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq45988
  have eq46039 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq46032
  have eq46040 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq46039
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46039
    | exact resolve eq46039 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46039
  have eq46161 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq46040 eq441
    | exact resolve eq441 eq46040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46491 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq45717
       have i₂ := eq45828 X0 x
       grind)
    | exact superpose eq45828 eq45717
    | exact resolve eq45717 eq45828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45717
  have eq46494 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq45828 X0 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq45828 X0 x
       grind)
    | exact superpose eq45828 eq18
    | (have j1 := eq45828 X0 y
       grind)
    | exact resolve eq18 eq45828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45828
  have eq46609 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq46491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46491
  have eq46660 : y = (M.op x y) ∨ x = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f46660_13 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f46660_14 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f46660_23 : y ≠ (M.op x y) := by grind
    have f46660_24 : x ≠ (M.op x y) := by grind
    have f46660_25 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
      intro X0
      first
      | (have j0 := f46660_14 X0
         grind)
      | (have r₁ := f46660_14 X0
         have r₂ := f46660_23
         grind)
      | exact resolve f46660_14 f46660_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f46660_26 : ∀ X0 : G, x = (M.op (M.op x y) X0) := by
      intro X0
      first
      | (have j0 := f46660_13 X0
         grind)
      | (have r₁ := f46660_13 X0
         have r₂ := f46660_23
         grind)
      | exact resolve f46660_13 f46660_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f46660_28 : x = (M.op x y) := by
      first
      | (have i₁ := f46660_26 x
         have i₂ := f46660_25 x
         grind)
      | exact superpose f46660_25 f46660_26
      | exact resolve f46660_26 f46660_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f46660_29 : False := by
      first
      | (have r₁ := f46660_28
         have r₂ := f46660_24
         grind)
      | exact resolve f46660_28 f46660_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f46660_29
  clear eq46609
  have eq46778 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq46660
       grind)
    | exact superpose eq46660 eq18
    | exact resolve eq18 eq46660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46660
  have eq47307 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46778 eq367
    | exact resolve eq367 eq46778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq46778
  have eq53862 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq46161 eq1254
    | exact resolve eq1254 eq46161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58356 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq53862
    | (have j0 := eq53862 (σ y)
       grind)
    | exact resolve eq53862 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53862
  have eq58425 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq58356 eq758
    | (have j0 := eq758 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq758 (M.op (σ x) (σ y))
       have r₂ := eq58356
       grind)
    | exact resolve eq758 eq58356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58356
  have eq58428 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq58425
  have eq58431 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq237 eq58428
    | exact resolve eq58428 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58428
  have eq58458 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq58431 eq46161
    | exact resolve eq46161 eq58431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58431
  have eq58541 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq58458 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58458
  have eq58667 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq58541 eq46040
    | exact resolve eq46040 eq58541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46040 eq58541
  have eq58790 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq58667
  have eq63822 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq720 y X0
       have i₂ := eq40721
       grind)
    | exact superpose eq40721 eq720
    | (have j0 := eq720 x x
       grind)
    | exact resolve eq720 eq40721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq40721
  have eq64247 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq63822 X0
       have j1 := eq758 x
       grind)
    | (have r₁ := eq63822 X0
       have r₂ := eq758 x
       grind)
    | exact resolve eq63822 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63822
  have eq64301 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq64247 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq64247
    | (have j0 := eq64247 X0
       grind)
    | exact resolve eq64247 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq64247
  have eq64321 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq47307 eq64301
    | (have j0 := eq64301 X0
       have j1 := eq47307 X0
       grind)
    | exact resolve eq64301 eq47307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64301
  have eq64324 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq47307 eq64321
    | (have j0 := eq64321 X0
       have j1 := eq47307 X0
       grind)
    | exact resolve eq64321 eq47307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47307 eq64321
  have eq64326 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq46494 eq64324
    | (have j0 := eq64324 X0
       have j1 := eq46494 X0
       grind)
    | exact resolve eq64324 eq46494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46494 eq64324
  have eq64327 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq64326 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64326
  have eq64947 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq64327 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64327
  have eq64948 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq64947
  have eq64982 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq64948 eq191
    | exact resolve eq191 eq64948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq64991 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq64948 eq330
    | exact resolve eq330 eq64948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq65004 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq64948 eq32886
    | exact resolve eq32886 eq64948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32886 eq64948
  have eq65075 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq65004
    | exact resolve eq65004 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65004
  have eq65078 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq64991
    | exact resolve eq64991 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64991
  have eq65147 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq64982 eq182
    | exact resolve eq182 eq64982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq64982
  have eq65379 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq65075 eq12
    | (have j0 := eq12 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq12 X0 (σ (M.op x y))
       have r₂ := eq65075
       grind)
    | exact resolve eq12 eq65075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65075
  have eq65438 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq65379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65379
  have eq77506 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq65438 eq441
    | (have j1 := eq65438 (σ x)
       grind)
    | exact resolve eq441 eq65438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq77571 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq65078 eq77506
    | exact resolve eq77506 eq65078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77506
  have eq77759 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq46161 eq77571
    | (have j0 := eq77571 X0
       have j1 := eq46161 X0
       grind)
    | exact resolve eq77571 eq46161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46161 eq77571
  have eq77880 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq77759
    | (have j0 := eq77759 X0
       grind)
    | exact resolve eq77759 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77759
  have eq80418 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq77880 eq1254
    | exact resolve eq1254 eq77880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq80587 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq80418
    | (have j0 := eq80418 (σ y)
       grind)
    | exact resolve eq80418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80418
  have eq80668 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80587 eq758
    | (have j0 := eq758 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq758 (M.op (σ x) (σ y))
       have r₂ := eq80587
       grind)
    | exact resolve eq758 eq80587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80587
  have eq80673 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq80668
  have eq80677 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq237 eq80673
    | exact resolve eq80673 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq80673
  have eq80717 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq80677 eq77880
    | exact resolve eq77880 eq80677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77880 eq80677
  have eq80813 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq80717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80717
  have eq81132 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80813 eq65438
    | exact resolve eq65438 eq80813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65438 eq80813
  have eq81138 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq81132
       have r₂ := eq27
       grind)
    | exact resolve eq81132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81132
  have eq81238 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65078 eq81138
    | exact resolve eq81138 eq65078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65078 eq81138
  have eq81287 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81238 eq27
    | exact resolve eq27 eq81238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81238
  have eq81372 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq81287
       have r₂ := eq58790
       grind)
    | exact resolve eq81287 eq58790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58790 eq81287
  have eq81402 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq81372 eq27
    | exact resolve eq27 eq81372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq81408 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq81372 eq240
    | exact resolve eq240 eq81372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq81830 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq81408 eq26
    | (have j1 := eq81408 (σ y) X0
       grind)
    | exact resolve eq26 eq81408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq81408
  have eq81987 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq81372 eq81830
    | exact resolve eq81830 eq81372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81372 eq81830
  have eq82180 : x = (k x (τ (σ x))) := by
    first
    | exact superpose eq81987 eq486
    | exact resolve eq486 eq81987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq81987
  have eq82345 : x = (k x x) := by
    first
    | exact superpose eq29 eq82180
    | exact resolve eq82180 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq82180
  have eq82458 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq758 x
       have i₂ := eq82345
       grind)
    | exact superpose eq82345 eq758
    | (have j0 := eq758 x
       grind)
    | (have r₁ := eq758 x
       have r₂ := eq82345
       grind)
    | exact resolve eq758 eq82345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq82345
  have eq82463 : x = (M.op x x) := by grind
  clear eq82458
  have eq82536 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq184 x X0 x
       have i₂ := eq82463
       grind)
    | exact superpose eq82463 eq184
    | exact resolve eq184 eq82463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq82598 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq82536 X0
       have i₂ := eq82463
       grind)
    | exact superpose eq82463 eq82536
    | exact resolve eq82536 eq82463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82463 eq82536
  have eq82641 : x = (M.op x y) := by
    first
    | (have i₁ := eq82598 x
       have i₂ := eq65147 x
       grind)
    | exact superpose eq65147 eq82598
    | exact resolve eq82598 eq65147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65147 eq82598
  have eq84437 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq82641
       grind)
    | exact superpose eq82641 eq22
    | exact resolve eq22 eq82641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq82641
  have eq84578 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq84437 eq20
    | exact resolve eq20 eq84437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq84437
  have eq84731 : False := by grind
  exact eq84731

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_x_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq24 eq35
  have eq64 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
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
  have eq69 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq44
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq144 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq65
    | exact resolve eq65 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq145 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq69
    | (have r₁ := eq69
       have r₂ := eq130
       grind)
    | exact resolve eq69 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq130
  have eq404 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq403
  have eq405 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq404
       have r₂ := eq144
       grind)
    | exact resolve eq404 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq404
  have eq408 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq405 eq117
    | exact resolve eq117 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq405
  have eq412 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq408
  have eq417 : x = (M.op x y) := by
    first
    | (have r₁ := eq412
       have r₂ := eq145
       grind)
    | exact resolve eq412 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq412
  have eq420 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq417 eq20
    | exact resolve eq20 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq423 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq417 eq64
    | exact resolve eq64 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq424 : x ≠ x ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq417 eq68
    | (have r₁ := eq68
       have r₂ := eq417
       grind)
    | exact resolve eq68 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq417
  have eq431 : x = y ∨ x = (k x y) := by grind
  clear eq424
  have eq438 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq420
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq420
    | exact resolve eq420 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq483 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq438 eq26
    | exact resolve eq26 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq657 : x = (k x y) := by
    first
    | (have r₁ := eq431
       have r₂ := eq423
       grind)
    | exact resolve eq431 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq431
  have eq662 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq657
       grind)
    | exact superpose eq657 eq44
    | exact resolve eq44 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq657
  have eq669 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq438 eq662
    | exact resolve eq662 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq671 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq669
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq669
    | exact resolve eq669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq669
  have eq672 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq438 eq671
    | exact resolve eq671 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq671
  have eq675 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq672 eq85
    | (have j0 := eq85 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq85 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq672
  have eq676 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq675
  have eq678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq483 eq676
    | exact resolve eq676 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq676
  have eq681 : False := by grind
  exact eq681

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq56 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 (M.op x y)))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq81
    | exact resolve eq81 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) X0) ∨ (M.op (M.op X1 (M.op X1 (M.op X2 X0))) X0) = (k X0 (M.op X1 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X0)))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X0)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X0)))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X2 X0))) X0) = (k X0 (M.op X1 (M.op X1 (M.op X2 X0)))) ∨ (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq105 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq131 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq148 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (M.op x y) ≠ (M.op x y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq215 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq215
       grind)
    | exact resolve eq13 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq224 : y = (k y (M.op x y)) := by grind
  clear eq223
  have eq227 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq224 eq93
    | exact resolve eq93 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq231 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq227
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq227
    | exact resolve eq227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq239 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq247 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq239 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq239
       grind)
    | exact resolve eq13 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq248 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq247
  have eq262 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X1
       have i₂ := eq60 X1 X0
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X0) X0
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq60 X1 X0
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq268 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq269 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq262 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq910 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq989 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq56 eq106
    | exact resolve eq106 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq8833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq8834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq8833
    | exact resolve eq8833 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8833
  have eq8845 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq8834
       have r₂ := eq27
       grind)
    | exact resolve eq8834 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8834
  have eq8848 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq8845
    | exact resolve eq8845 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8845
  have eq8860 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8848 eq268
    | exact resolve eq268 eq8848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq8848
  have eq9001 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8860 eq55
    | exact resolve eq55 eq8860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq8860
  have eq9022 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq9001
    | exact resolve eq9001 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9001
  have eq9025 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq9022
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq9022
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq9022
       have r₂ := eq13 x y
       grind)
    | exact resolve eq9022 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9022
  have eq9027 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq9025
       grind)
    | exact superpose eq9025 eq44
    | exact resolve eq44 eq9025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq9035 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq9025
       grind)
    | exact superpose eq9025 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq9025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9025
  have eq9036 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9035
  have eq9039 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9036
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9036
    | exact resolve eq9036 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9036
  have eq9040 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9039
  have eq9048 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9027
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9027
    | exact resolve eq9027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9027
  have eq9169 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq269 y x
       have i₂ := eq9040
       grind)
    | exact superpose eq9040 eq269
    | exact resolve eq269 eq9040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9040
  have eq9180 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9169
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9169
    | exact resolve eq9169 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9169
  have eq9183 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9180
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9180
    | exact resolve eq9180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9180
  have eq9184 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9183
  have eq9199 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9048 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq9048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9048
  have eq9200 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9199
  have eq9205 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9200
    | exact resolve eq9200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9200
  have eq9206 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9205
  have eq9419 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq9184
       grind)
    | exact superpose eq9184 eq91
    | exact resolve eq91 eq9184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9184
  have eq9435 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9419
    | exact resolve eq9419 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9419
  have eq9451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9206 eq269
    | exact resolve eq269 eq9206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9206
  have eq9464 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9451
    | exact resolve eq9451 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9451
  have eq9467 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9464
    | exact resolve eq9464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9464
  have eq9468 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9467
  have eq9671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9468 eq9435
    | exact resolve eq9435 eq9468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9435 eq9468
  have eq9674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9671
  have eq9676 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9674
       have r₂ := eq27
       grind)
    | exact resolve eq9674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9674
  have eq9688 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9676 eq248
    | exact resolve eq248 eq9676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq9676
  have eq9705 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9688 eq101
    | exact resolve eq101 eq9688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq9688
  have eq9730 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq9705
    | exact resolve eq9705 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9705
  have eq9733 : y = (k y x) := by
    first
    | (have r₁ := eq9730
       have r₂ := eq50
       grind)
    | exact resolve eq9730 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq9730
  have eq9736 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq91
    | exact resolve eq91 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9745 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9746 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq9745
  have eq9749 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9746
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9746
    | exact resolve eq9746 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9746
  have eq9757 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9736
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9736
    | exact resolve eq9736 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9736
  have eq9793 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq9749
       grind)
    | exact superpose eq9749 eq14
    | exact resolve eq14 eq9749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9802 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq269 y x
       have i₂ := eq9749
       grind)
    | exact superpose eq9749 eq269
    | exact resolve eq269 eq9749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9749
  have eq9817 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9802
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq9802
    | exact resolve eq9802 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9733 eq9802
  have eq9820 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9817
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9817
    | exact resolve eq9817 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9817
  have eq9822 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9820
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9820
    | exact resolve eq9820 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9820
  have eq9823 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq9822
  have eq9965 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq910 y x
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq910
    | (have j0 := eq910 y x
       grind)
    | exact resolve eq910 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq910
  have eq10048 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9757 eq9965
    | (have r₁ := eq9965
       have r₂ := eq9757
       grind)
    | exact resolve eq9965 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9965
  have eq10144 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10048
       have r₂ := eq24
       grind)
    | exact resolve eq10048 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10048
  have eq10238 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10144
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10144
    | exact resolve eq10144 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10144
  have eq10326 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10238
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10238
    | exact resolve eq10238 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10238
  have eq10413 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10326
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10326
    | exact resolve eq10326 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10326
  have eq10481 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10413
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10413
    | exact resolve eq10413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10413
  have eq10496 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10481
    | exact resolve eq10481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481
  have eq10516 : (σ (k y y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9823 eq93
    | exact resolve eq93 eq9823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq10524 : (σ (k y y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9823 eq131
    | exact resolve eq131 eq9823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq9823
  have eq10610 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10524
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq10524
    | exact resolve eq10524 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10524
  have eq10617 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq231 eq10516
    | exact resolve eq10516 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq10516
  have eq10631 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10617
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq10617
    | exact resolve eq10617 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq10617
  have eq10883 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10496 eq14
    | exact resolve eq14 eq10496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10892 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10496 eq269
    | exact resolve eq269 eq10496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq10496
  have eq10908 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9757 eq10892
    | exact resolve eq10892 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757 eq10892
  have eq10911 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10908
    | exact resolve eq10908 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10908
  have eq10913 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10911
    | exact resolve eq10911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10911
  have eq10914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10913
  have eq10936 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq21869 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10610 eq10631
    | exact resolve eq10631 eq10610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10610 eq10631
  have eq21890 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21869
  have eq22937 : (τ (σ y)) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21890 eq148
    | exact resolve eq148 eq21890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq21890
  have eq22965 : y = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq22937
    | exact resolve eq22937 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22937
  have eq23056 : y = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22965 eq989
    | exact resolve eq989 eq22965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq22965
  have eq23069 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq23056
  have eq23111 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23069 eq56
    | exact resolve eq56 eq23069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq23069
  have eq37504 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10883
    | (have j0 := eq10883 (σ x)
       grind)
    | exact resolve eq10883 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10883
  have eq37849 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10914 eq37504
    | exact resolve eq37504 eq10914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37504
  have eq37959 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37849
       have r₂ := eq10936
       grind)
    | exact resolve eq37849 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37849
  have eq37961 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq37959
    | exact resolve eq37959 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37959
  have eq37962 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10914 eq37961
    | exact resolve eq37961 eq10914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10914 eq37961
  have eq38040 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37962
       have r₂ := eq10936
       grind)
    | exact resolve eq37962 eq10936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10936 eq37962
  have eq38041 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq38040
    | exact resolve eq38040 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq38040
  have eq38042 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38041
  have eq38044 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq38042 eq27
    | exact resolve eq27 eq38042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq38042
  have eq41076 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9793 y
       have i₂ := eq23111
       grind)
    | exact superpose eq23111 eq9793
    | exact resolve eq9793 eq23111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9793 eq23111
  have eq41209 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq41076
  have eq41224 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41209
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41209
    | exact resolve eq41209 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41209
  have eq41225 : x = (M.op x y) := by grind
  clear eq41224
  have eq41230 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq41225 eq20
    | exact resolve eq20 eq41225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41225
  have eq41369 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41230
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41230
    | exact resolve eq41230 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq41230
  have eq41373 : False := by grind
  exact eq41373

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_x_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq40
    | exact resolve eq40 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40
  have eq62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq239 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq246 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       have j1 := eq91 X1 X0
       grind)
    | (have r₁ := eq239 X1 X0
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq239 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq239 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq239
  have eq285 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246
    | exact resolve eq246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq246 (σ X1) X0
       grind)
    | exact superpose eq246 eq15
    | (have j1 := eq246 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq323 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq285 X0 (τ X1)
       grind)
    | exact superpose eq285 eq18
    | (have j1 := eq285 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq285
  have eq777 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq323
    | exact resolve eq323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq812 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq777
    | (have j0 := eq777 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq777 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1524 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq290 x y
       grind)
    | exact superpose eq290 eq16
    | (have j1 := eq290 x y
       grind)
    | exact resolve eq16 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq1589 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1524
       have i₂ := eq812 y x
       grind)
    | exact superpose eq812 eq1524
    | (have j1 := eq812 (σ x) (σ y)
       grind)
    | (have r₁ := eq1524
       have r₂ := eq812 y x
       grind)
    | (have r₁ := eq1524
       have r₂ := eq812 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1524
       have r₂ := eq812 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1524 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq1524
  have eq1590 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1589
  have eq1594 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1590
       grind)
    | exact superpose eq1590 eq10
    | exact resolve eq10 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1637 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1594
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1594
    | exact resolve eq1594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1638 : x = y := by grind
  clear eq1637
  have eq1751 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1638
       grind)
    | exact superpose eq1638 eq16
    | exact resolve eq16 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1752 : False := by grind
  exact eq1752
