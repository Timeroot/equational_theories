import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq102
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113
    | (have j0 := eq113 X0
       grind)
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq114 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq114 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq115 (σ X0)
       grind)
    | exact superpose eq115 eq15
    | exact resolve eq15 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq117
    | exact resolve eq117 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq117
  have eq165 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq16
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq16 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1180 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq170 (τ X0) (τ X1)
       have i₂ := eq72 X1 X0
       grind)
    | exact superpose eq72 eq170
    | (have j0 := eq170 (τ X0) (τ X1)
       grind)
    | exact resolve eq170 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1199 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1180 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1180
    | (have j0 := eq1180 X0 X1
       grind)
    | exact resolve eq1180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1207 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1213 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1207
    | (have j0 := eq1207 X0 X1
       grind)
    | exact resolve eq1207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1215 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1213 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1213
    | (have j0 := eq1213 X0 X1
       grind)
    | exact resolve eq1213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1216 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1215 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1215
    | (have j0 := eq1215 X0 X1
       grind)
    | exact resolve eq1215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1217 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1216 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1216
    | (have j0 := eq1216 X0 X1
       grind)
    | exact resolve eq1216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1851 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq165
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq165
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq165
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq165
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq165 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq1852 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1851
  have eq11277 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1852
       grind)
    | exact superpose eq1852 eq16
    | exact resolve eq16 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq11278 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11277
       have r₂ := eq126 x
       grind)
    | exact resolve eq11277 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11277
  have eq11281 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq11278
       grind)
    | exact superpose eq11278 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq11278
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11278
       grind)
    | exact resolve eq12 eq11278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11278
  have eq11284 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11281
  have eq11289 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq170 x y
       have i₂ := eq11284
       grind)
    | exact superpose eq11284 eq170
    | (have j0 := eq170 x y
       grind)
    | exact resolve eq170 eq11284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq11284
  have eq11296 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11289
  have eq11297 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11296
  have eq11380 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11297
       grind)
    | exact superpose eq11297 eq16
    | exact resolve eq16 eq11297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11384 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq11297
       grind)
    | exact superpose eq11297 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11297
       grind)
    | exact resolve eq12 eq11297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11297
  have eq11387 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11384
  have eq11389 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq11387
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq11387
    | exact resolve eq11387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11387
  have eq11574 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11389
       grind)
    | exact superpose eq11389 eq10
    | exact resolve eq10 eq11389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11389
  have eq11659 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq11574
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11574
    | exact resolve eq11574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11574
  have eq11667 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11659
       grind)
    | exact superpose eq11659 eq16
    | exact resolve eq16 eq11659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11659
  have eq11668 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq11667
       have r₂ := eq126 x
       grind)
    | exact resolve eq11667 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11667
  have eq11841 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq11668
       grind)
    | exact superpose eq11668 eq10
    | exact resolve eq10 eq11668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11668
  have eq11929 : x = (k x y) := by
    first
    | (have i₁ := eq11841
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11841
    | exact resolve eq11841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11841
  have eq11945 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1217 x y
       have i₂ := eq11929
       grind)
    | exact superpose eq11929 eq1217
    | (have j0 := eq1217 x y
       grind)
    | (have r₁ := eq1217 x y
       have r₂ := eq11929
       grind)
    | exact resolve eq1217 eq11929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq11929
  have eq11949 : x = (M.op x y) ∨ x = y := by grind
  clear eq11945
  have eq12105 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11380
       have i₂ := eq11949
       grind)
    | exact superpose eq11949 eq11380
    | exact resolve eq11380 eq11949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11380 eq11949
  have eq12112 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq12105
  have eq12113 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12112
       grind)
    | exact superpose eq12112 eq16
    | exact resolve eq16 eq12112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112
  have eq12118 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq12113
       have r₂ := eq126 x
       grind)
    | exact resolve eq12113 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12113
  have eq12243 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12118
       grind)
    | exact superpose eq12118 eq16
    | exact resolve eq16 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12244 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12118
       grind)
    | exact superpose eq12118 eq10
    | exact resolve eq10 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12118
  have eq12331 : x = y := by
    first
    | (have i₁ := eq12244
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12244
    | exact resolve eq12244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12244
  have eq12332 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12243
       have i₂ := eq126 x
       grind)
    | exact superpose eq126 eq12243
    | exact resolve eq12243 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq12243
  have eq12337 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12332
       have i₂ := eq12331
       grind)
    | exact superpose eq12331 eq12332
    | exact resolve eq12332 eq12331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12331 eq12332
  have eq12338 : False := by grind
  exact eq12338

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq20 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq45 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq20 X0
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq45 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq66 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq71
  have eq101 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq126 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq101
    | (have j0 := eq101 X0 X1
       grind)
    | exact resolve eq101 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq132 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq126 X0 X1
       have j1 := eq66 X1 X0
       grind)
    | (have r₁ := eq126 X1 X0
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq126 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq126
  have eq463 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (σ X1))) = X2 ∨ (k X2 (k X0 (σ X1))) = (M.op X2 (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq132
    | exact resolve eq132 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq473 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq132 (σ X0) X1
       grind)
    | exact superpose eq132 eq15
    | (have j1 := eq132 (σ X0) X1
       grind)
    | exact resolve eq15 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq497 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq463 (τ X1) X0
       grind)
    | exact superpose eq463 eq18
    | (have j1 := eq463 (τ X1) X0
       grind)
    | exact resolve eq18 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq463
  have eq678 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       have j1 := eq46 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq46 X0
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq872 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq497 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq497
    | exact resolve eq497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq931 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq872
    | (have j0 := eq872 X0 X1
       grind)
    | exact resolve eq872 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq1644 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq473 x y
       grind)
    | exact superpose eq473 eq16
    | (have j1 := eq473 x y
       grind)
    | exact resolve eq16 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1671 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq473 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq2034 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1644
       have i₂ := eq931 y x
       grind)
    | exact superpose eq931 eq1644
    | (have j1 := eq931 (σ y) (σ x)
       grind)
    | (have r₁ := eq1644
       have r₂ := eq931 y x
       grind)
    | exact resolve eq1644 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq2035 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2034
  have eq6717 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (M.op (k X1 (σ X2)) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (k X1 (σ X2))
       have i₂ := eq464 X1 X2 X0
       grind)
    | exact superpose eq464 eq13
    | (have j0 := eq13 X0 (k X1 (σ X2))
       have j1 := eq464 X1 X2 X0
       grind)
    | (have r₁ := eq13 X2 (k X0 (σ X1))
       have r₂ := eq464 X0 X1 X2
       grind)
    | exact resolve eq13 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq6728 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = X0 ∨ (M.op (k X1 (σ X2)) (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6717 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717
  have eq6733 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq6728 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq6728 (k X1 (σ X2)) X1 X2
       have r₂ := eq12 (k X1 (σ X2)) (k X1 (σ X2))
       grind)
    | (have r₁ := eq6728 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq6728 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6728
  have eq13437 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq678 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq13441 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13437 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq13437
    | (have j0 := eq13437 X0
       grind)
    | exact resolve eq13437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13437
  have eq13442 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13441
  have eq20491 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 (σ X2))) ≠ X0 ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq6733 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733
  have eq20554 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X0)) ≠ X1 ∨ (k X1 (k X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20491 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20491
    | exact resolve eq20491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20491
  have eq20691 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20554 (M.op X0 X0) X1 X0
       have i₂ := eq13442 X0
       grind)
    | exact superpose eq13442 eq20554
    | exact resolve eq20554 eq13442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13442 eq20554
  have eq20853 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20691 y x
       have i₂ := eq2035
       grind)
    | exact superpose eq2035 eq20691
    | (have j0 := eq20691 y x
       grind)
    | (have r₁ := eq20691 y x
       have r₂ := eq2035
       grind)
    | (have r₁ := eq20691 (σ y) (σ x)
       have r₂ := eq2035
       grind)
    | exact resolve eq20691 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq20855 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20853
  have eq24948 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1671 x y
       have i₂ := eq20855
       grind)
    | exact superpose eq20855 eq1671
    | (have j0 := eq1671 x y
       grind)
    | exact resolve eq1671 eq20855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671 eq20855
  have eq24984 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24948
  have eq24985 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24984
  have eq25004 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24985
       grind)
    | exact superpose eq24985 eq16
    | exact resolve eq16 eq24985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25014 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq20691 (σ y) (σ x)
       have i₂ := eq24985
       grind)
    | exact superpose eq24985 eq20691
    | (have j0 := eq20691 (σ y) (σ x)
       grind)
    | (have r₁ := eq20691 (σ y) (σ x)
       have r₂ := eq24985
       grind)
    | exact resolve eq20691 eq24985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20691 eq24985
  have eq25018 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq25014
  have eq25020 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq25018
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq25018
    | exact resolve eq25018 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25018
  have eq25080 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq931 y x
       have i₂ := eq25020
       grind)
    | exact superpose eq25020 eq931
    | (have j0 := eq931 y x
       grind)
    | exact resolve eq931 eq25020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq25020
  have eq25211 : x = (M.op x y) := by
    first
    | (have r₁ := eq25080
       have r₂ := eq25004
       grind)
    | exact resolve eq25080 eq25004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25080
  have eq25444 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq25004
       have i₂ := eq25211
       grind)
    | exact superpose eq25211 eq25004
    | exact resolve eq25004 eq25211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25004 eq25211
  have eq25462 : False := by grind
  exact eq25462

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1031 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq562 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq595 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq618 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq638 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq618 x y
       grind)
    | exact superpose eq618 eq16
    | (have j1 := eq618 x y
       grind)
    | exact resolve eq16 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq618 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq14697 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq592
    | exact resolve eq592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq14793 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14697 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14697
    | (have j0 := eq14697 X0 X1
       grind)
    | exact resolve eq14697 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14697
  have eq29953 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq638
       have i₂ := eq14793 y x
       grind)
    | exact superpose eq14793 eq638
    | (have j1 := eq14793 y x
       grind)
    | (have r₁ := eq638
       have r₂ := eq14793 y x
       grind)
    | (have r₁ := eq638
       have r₂ := eq14793 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq638
       have r₂ := eq14793 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq638 eq14793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq14793
  have eq29954 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq29953
  have eq37099 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq642
    | (have j0 := eq642 (τ X0) (τ X1)
       grind)
    | exact resolve eq642 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq37249 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37099 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq37099
    | (have j0 := eq37099 X0 X1
       grind)
    | exact resolve eq37099 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37099
  have eq37318 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37249 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq37249
    | (have j0 := eq37249 X0 X1
       grind)
    | exact resolve eq37249 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37249
  have eq37381 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37318 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq37318
    | (have j0 := eq37318 X0 X1
       grind)
    | exact resolve eq37318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37318
  have eq37423 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37381 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37381
    | (have j0 := eq37381 X0 X1
       grind)
    | exact resolve eq37381 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37381
  have eq37457 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37423 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq37423
    | (have j0 := eq37423 X0 X1
       grind)
    | exact resolve eq37423 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq37423
  have eq37486 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37457 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq37457
    | (have j0 := eq37457 X0 X1
       grind)
    | exact resolve eq37457 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37457
  have eq37503 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37486 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37486
    | (have j0 := eq37486 X0 X1
       grind)
    | exact resolve eq37486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37486
  have eq92772 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29954
       grind)
    | exact superpose eq29954 eq16
    | exact resolve eq16 eq29954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29954
  have eq92773 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq92772
       have r₂ := eq22 x
       grind)
    | exact resolve eq92772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92772
  have eq92777 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq92773
       grind)
    | exact superpose eq92773 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq92773
       grind)
    | exact resolve eq13 eq92773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92773
  have eq92780 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq92777
  have eq97617 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92780
       grind)
    | exact superpose eq92780 eq16
    | exact resolve eq16 eq92780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92780
  have eq97618 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq97617
       have r₂ := eq22 x
       grind)
    | exact resolve eq97617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97617
  have eq97621 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq562 x (σ y)
       have i₂ := eq97618
       grind)
    | exact superpose eq97618 eq562
    | (have j0 := eq562 x (σ y)
       grind)
    | (have r₁ := eq562 x (σ y)
       have r₂ := eq97618
       grind)
    | exact resolve eq562 eq97618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97618
  have eq97638 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq97621
  have eq97639 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq97638
  have eq97645 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq97639
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq97639
    | exact resolve eq97639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97639
  have eq97655 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq642 x y
       have i₂ := eq97645
       grind)
    | exact superpose eq97645 eq642
    | (have j0 := eq642 x y
       grind)
    | (have r₁ := eq642 x y
       have r₂ := eq97645
       grind)
    | exact resolve eq642 eq97645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97645
  have eq97682 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq97655
  have eq97683 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq97682
  have eq97688 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq642 x y
       grind)
    | (have r₁ := eq97683
       have r₂ := eq642 x y
       grind)
    | exact resolve eq97683 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq97683
  have eq97691 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97688
       grind)
    | exact superpose eq97688 eq16
    | exact resolve eq16 eq97688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97692 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq562 x (σ y)
       have i₂ := eq97688
       grind)
    | exact superpose eq97688 eq562
    | (have j0 := eq562 x (σ y)
       grind)
    | (have r₁ := eq562 x (σ y)
       have r₂ := eq97688
       grind)
    | exact resolve eq562 eq97688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq97688
  have eq97709 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq97692
  have eq97710 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq97709
  have eq97716 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq97710
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq97710
    | exact resolve eq97710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97710
  have eq98264 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq97716
       grind)
    | exact superpose eq97716 eq10
    | exact resolve eq10 eq97716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97716
  have eq98458 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq98264
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq98264
    | exact resolve eq98264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98264
  have eq98460 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98458
       grind)
    | exact superpose eq98458 eq16
    | exact resolve eq16 eq98458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98458
  have eq98461 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq98460
       have r₂ := eq22 x
       grind)
    | exact resolve eq98460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98460
  have eq98477 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq98461
       grind)
    | exact superpose eq98461 eq10
    | exact resolve eq10 eq98461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98461
  have eq98672 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq98477
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq98477
    | exact resolve eq98477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98477
  have eq98696 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq37503 x y
       have i₂ := eq98672
       grind)
    | exact superpose eq98672 eq37503
    | (have j0 := eq37503 x y
       grind)
    | (have r₁ := eq37503 x y
       have r₂ := eq98672
       grind)
    | exact resolve eq37503 eq98672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37503 eq98672
  have eq98706 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq98696
  have eq98710 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq97691
       have i₂ := eq98706
       grind)
    | exact superpose eq98706 eq97691
    | exact resolve eq97691 eq98706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97691 eq98706
  have eq98724 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq98710
  have eq98731 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98724
       grind)
    | exact superpose eq98724 eq16
    | exact resolve eq16 eq98724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98724
  have eq98734 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq98731
       have r₂ := eq22 x
       grind)
    | exact resolve eq98731 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98731
  have eq98735 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98734
       grind)
    | exact superpose eq98734 eq16
    | exact resolve eq16 eq98734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98736 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq98734
       grind)
    | exact superpose eq98734 eq10
    | exact resolve eq10 eq98734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98734
  have eq98930 : x = y := by
    first
    | (have i₁ := eq98736
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq98736
    | exact resolve eq98736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98736
  have eq98931 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq98735
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq98735
    | exact resolve eq98735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq98735
  have eq98932 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq98931
       have i₂ := eq98930
       grind)
    | exact superpose eq98930 eq98931
    | exact resolve eq98931 eq98930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98930 eq98931
  have eq98933 : False := by grind
  exact eq98933

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1031 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq226 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq228 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq605 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq226 x y
       grind)
    | exact superpose eq226 eq16
    | (have j1 := eq226 x y
       grind)
    | exact resolve eq16 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq4814 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq228 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq228
    | exact resolve eq228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq4915 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4814 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4814
    | (have j0 := eq4814 X0 X1
       grind)
    | exact resolve eq4814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814
  have eq5080 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq609 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq609
    | (have j0 := eq609 (τ X0) (τ X1)
       grind)
    | exact resolve eq609 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq5098 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5080 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5080
    | (have j0 := eq5080 X0 X1
       grind)
    | exact resolve eq5080 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080
  have eq5110 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5098 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5098
    | (have j0 := eq5098 X0 X1
       grind)
    | exact resolve eq5098 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5098
  have eq5119 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5110 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5110
    | (have j0 := eq5110 X0 X1
       grind)
    | exact resolve eq5110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq5126 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5119 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5119
    | (have j0 := eq5119 X0 X1
       grind)
    | exact resolve eq5119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5119
  have eq5128 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5126 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5126
    | (have j0 := eq5126 X0 X1
       grind)
    | exact resolve eq5126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5126
  have eq5130 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5128 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5128
    | (have j0 := eq5128 X0 X1
       grind)
    | exact resolve eq5128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5128
  have eq14740 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq605
       have i₂ := eq4915 x y
       grind)
    | exact superpose eq4915 eq605
    | (have j1 := eq4915 (σ x) (σ y)
       grind)
    | (have r₁ := eq605
       have r₂ := eq4915 x y
       grind)
    | (have r₁ := eq605
       have r₂ := eq4915 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq605
       have r₂ := eq4915 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq605 eq4915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq4915
  have eq14741 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14740
  have eq22189 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14741
       grind)
    | exact superpose eq14741 eq16
    | exact resolve eq16 eq14741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14741
  have eq22190 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22189
       have r₂ := eq22 x
       grind)
    | exact resolve eq22189 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22189
  have eq22192 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq22190
       grind)
    | exact superpose eq22190 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22190
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22190
       grind)
    | exact resolve eq13 eq22190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22190
  have eq22195 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22192
  have eq23432 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22195
       grind)
    | exact superpose eq22195 eq16
    | exact resolve eq16 eq22195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22195
  have eq23433 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq23432
       have r₂ := eq22 x
       grind)
    | exact resolve eq23432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23432
  have eq23437 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq23433
       grind)
    | exact superpose eq23433 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq23433
       grind)
    | exact resolve eq13 eq23433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23433
  have eq23442 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq23437
  have eq23443 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq23442
  have eq23446 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq23443
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq23443
    | exact resolve eq23443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23443
  have eq23460 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq609 x y
       have i₂ := eq23446
       grind)
    | exact superpose eq23446 eq609
    | (have j0 := eq609 x y
       grind)
    | (have r₁ := eq609 x y
       have r₂ := eq23446
       grind)
    | exact resolve eq609 eq23446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23446
  have eq23475 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq23460
  have eq23476 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq23475
  have eq23481 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq609 x y
       grind)
    | (have r₁ := eq23476
       have r₂ := eq609 x y
       grind)
    | exact resolve eq23476 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq23476
  have eq23485 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23481
       grind)
    | exact superpose eq23481 eq16
    | exact resolve eq16 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23487 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq23481
       grind)
    | exact superpose eq23481 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq23481
       grind)
    | exact resolve eq13 eq23481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23481
  have eq23492 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq23487
  have eq23493 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq23492
  have eq23496 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq23493
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq23493
    | exact resolve eq23493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23493
  have eq23507 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23496
       grind)
    | exact superpose eq23496 eq10
    | exact resolve eq10 eq23496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23496
  have eq23573 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq23507
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23507
    | exact resolve eq23507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23507
  have eq23729 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23573
       grind)
    | exact superpose eq23573 eq16
    | exact resolve eq16 eq23573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23573
  have eq23730 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq23729
       have r₂ := eq22 x
       grind)
    | exact resolve eq23729 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23729
  have eq23741 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq23730
       grind)
    | exact superpose eq23730 eq10
    | exact resolve eq10 eq23730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23730
  have eq23808 : y = (k x y) := by
    first
    | (have i₁ := eq23741
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq23741
    | exact resolve eq23741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23741
  have eq23823 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5130 x y
       have i₂ := eq23808
       grind)
    | exact superpose eq23808 eq5130
    | (have j0 := eq5130 x y
       grind)
    | (have r₁ := eq5130 x y
       have r₂ := eq23808
       grind)
    | exact resolve eq5130 eq23808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5130 eq23808
  have eq23830 : y = (M.op x y) ∨ x = y := by grind
  clear eq23823
  have eq23834 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23485
       have i₂ := eq23830
       grind)
    | exact superpose eq23830 eq23485
    | exact resolve eq23485 eq23830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23485 eq23830
  have eq23845 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq23834
  have eq23846 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23845
       grind)
    | exact superpose eq23845 eq16
    | exact resolve eq16 eq23845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23845
  have eq23851 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq23846
       have r₂ := eq22 x
       grind)
    | exact resolve eq23846 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23846
  have eq23852 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23851
       grind)
    | exact superpose eq23851 eq16
    | exact resolve eq16 eq23851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23853 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23851
       grind)
    | exact superpose eq23851 eq10
    | exact resolve eq10 eq23851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23851
  have eq23919 : x = y := by
    first
    | (have i₁ := eq23853
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23853
    | exact resolve eq23853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23853
  have eq23920 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23852
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq23852
    | exact resolve eq23852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23852
  have eq23921 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23920
       have i₂ := eq23919
       grind)
    | exact superpose eq23919 eq23920
    | exact resolve eq23920 eq23919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23919 eq23920
  have eq23922 : False := by grind
  exact eq23922

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxx_pyy_pxy_Equation1052 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq85 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq61 X1
       grind)
    | exact superpose eq61 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq61 X1
       grind)
    | exact superpose eq61 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq201 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq23
    | exact resolve eq23 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ X1) X1
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq273 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq270 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq270 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq61 X1
       grind)
    | exact superpose eq61 eq237
    | (have j0 := eq237 X0 X1
       grind)
    | exact resolve eq237 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq296 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq61 X1
       grind)
    | exact superpose eq61 eq289
    | (have j0 := eq289 X0 X1
       grind)
    | exact resolve eq289 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq655 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq201 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq23 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq23 eq201
    | exact resolve eq201 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq725 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 X1
       have i₂ := eq61 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq61 eq655
    | exact resolve eq655 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq655
  have eq731 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq23 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq23 eq725
    | exact resolve eq725 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq725
  have eq1310 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1314 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1310 X0 X1
       have j1 := eq296 X0 X1
       grind)
    | (have r₁ := eq1310 X0 X1
       have r₂ := eq296 X0 X1
       grind)
    | exact resolve eq1310 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq1310
  have eq1495 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq273 (τ X0) X1
       grind)
    | exact superpose eq273 eq17
    | (have j1 := eq273 X0 X1
       grind)
    | exact resolve eq17 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq273
  have eq6177 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1314 X1 X0
       grind)
    | exact superpose eq1314 eq10
    | (have j1 := eq1314 X1 X0
       grind)
    | exact resolve eq10 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq6212 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6177 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6177
    | (have j0 := eq6177 X0 X1
       grind)
    | exact resolve eq6177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6177
  have eq118557 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1495 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1495
    | (have j0 := eq1495 X0 X1
       grind)
    | exact resolve eq1495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq119423 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118557 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq118557
    | (have j0 := eq118557 X0 X1
       grind)
    | exact resolve eq118557 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118557
  have eq132626 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6212 y x
       grind)
    | exact superpose eq6212 eq16
    | (have j1 := eq6212 y x
       grind)
    | exact resolve eq16 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6212
  have eq133155 : y = (M.op y y) := by
    first
    | (have j1 := eq119423 x y
       grind)
    | (have r₁ := eq132626
       have r₂ := eq119423 x y
       grind)
    | exact resolve eq132626 eq119423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119423 eq132626
  have eq133482 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq30 y x
       have i₂ := eq133155
       grind)
    | exact superpose eq133155 eq30
    | exact resolve eq30 eq133155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq133515 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq731 y X0
       have i₂ := eq133155
       grind)
    | exact superpose eq133155 eq731
    | exact resolve eq731 eq133155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq133753 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq133515 X0
       have i₂ := eq133155
       grind)
    | exact superpose eq133155 eq133515
    | exact resolve eq133515 eq133155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133515
  have eq133783 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq133482 X0
       have i₂ := eq133155
       grind)
    | exact superpose eq133155 eq133482
    | exact resolve eq133482 eq133155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133155 eq133482
  have eq136877 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133753 (σ x)
       grind)
    | exact superpose eq133753 eq16
    | exact resolve eq16 eq133753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133753
  have eq136902 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq136877
       have i₂ := eq133783 x
       grind)
    | exact superpose eq133783 eq136877
    | exact resolve eq136877 eq133783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133783 eq136877
  have eq136903 : False := by grind
  exact eq136903

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_y_pyx_Equation1061 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq120
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq123
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq214 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq221 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq386 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq874 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq857 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq857
    | (have j0 := eq857 X0 x
       grind)
    | exact resolve eq857 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq3103 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq386
    | exact resolve eq386 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq3286 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3103 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq3103
    | exact resolve eq3103 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3308 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3286 X0 X1 X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq3286
    | exact resolve eq3286 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq3325 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3308 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq3308
    | exact resolve eq3308 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3308
  have eq3342 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3325 X0 X1 X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq3325
    | exact resolve eq3325 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325
  have eq18318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq18318
    | exact resolve eq18318 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18318
  have eq18330 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq18319
       have r₂ := eq28
       grind)
    | exact resolve eq18319 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18319
  have eq18334 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq18330
    | exact resolve eq18330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18330
  have eq18347 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (k (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq18334 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18334
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18334
       grind)
    | exact resolve eq12 eq18334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18334
  have eq19445 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq874 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq874
    | (have j0 := eq874 y
       grind)
    | exact resolve eq874 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq19540 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19445
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq19445
    | exact resolve eq19445 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19445
  have eq19587 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19540
    | exact resolve eq19540 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19540
  have eq19595 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19587
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq19587
    | exact resolve eq19587 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19587
  have eq19601 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19595
    | exact resolve eq19595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19595
  have eq21270 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq18347
    | (have j0 := eq18347 (σ x)
       grind)
    | (have r₁ := eq18347 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq18347 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18347
  have eq21271 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq21270
  have eq21272 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq21271
  have eq21282 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21272 eq105
    | exact resolve eq105 eq21272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq21272
  have eq21291 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq21282
  have eq21310 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq21291
       grind)
    | exact superpose eq21291 eq96
    | exact resolve eq96 eq21291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq21321 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (k y X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq21291
       grind)
    | exact superpose eq21291 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq21291
       grind)
    | exact resolve eq12 eq21291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291
  have eq21349 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq21310
    | exact resolve eq21310 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21310
  have eq120924 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21321 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21321
    | (have j0 := eq21321 x
       grind)
    | (have r₁ := eq21321 x
       have r₂ := eq19
       grind)
    | exact resolve eq21321 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21321
  have eq120925 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq120924
  have eq120926 : x = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq120925
  have eq120929 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq120926
       grind)
    | exact superpose eq120926 eq90
    | exact resolve eq90 eq120926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq120926
  have eq121013 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120929
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq120929
    | exact resolve eq120929 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120929
  have eq121074 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq121013 eq19601
    | exact resolve eq19601 eq121013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19601 eq121013
  have eq121130 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq121074
  have eq121171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq121130 eq21349
    | exact resolve eq21349 eq121130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121130
  have eq121313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq121171
  have eq121328 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq121313
       have r₂ := eq28
       grind)
    | exact resolve eq121313 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121313
  have eq121336 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq121328 eq221
    | exact resolve eq221 eq121328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq121328
  have eq122333 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f122333_15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
      intro X0 X1 X2
      grind
    have f122333_16 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      grind
    have f122333_25 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f122333_26 : x ≠ y := by grind
    have f122333_27 : (σ x) ≠ (σ y) := by grind
    have f122333_28 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f122333_30 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f122333_16 X0
         grind)
      | (have r₁ := f122333_16 X0
         have r₂ := f122333_26
         grind)
      | exact resolve f122333_16 f122333_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122333_31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f122333_30 X0
         grind)
      | (have r₁ := f122333_30 X0
         have r₂ := f122333_27
         grind)
      | exact resolve f122333_30 f122333_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122333_32 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f122333_31 X0
         grind)
      | (have r₁ := f122333_31 X0
         have r₂ := f122333_28
         grind)
      | exact resolve f122333_31 f122333_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122333_67 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f122333_15 (σ y) X0 (σ x)
         have i₂ := f122333_32 (σ y)
         grind)
      | exact superpose f122333_32 f122333_15
      | exact resolve f122333_15 f122333_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122333_77 : X0 ≠ X0 := by
      first
      | (have i₁ := f122333_25
         have i₂ := f122333_67 X0
         grind)
      | exact superpose f122333_67 f122333_25
      | (have r₁ := f122333_25
         have r₂ := f122333_67 X0
         grind)
      | exact resolve f122333_25 f122333_67
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122333_78 : False := by grind
    exact f122333_78
  clear eq56 eq121336
  have eq122953 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq122333 eq21349
    | exact resolve eq21349 eq122333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21349
  have eq123072 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq122953
  have eq123190 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq123072 eq30
    | exact resolve eq30 eq123072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123072
  have eq123343 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq123190
    | exact resolve eq123190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123190
  have eq123344 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq123343
  have eq123365 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq123344 eq30
    | exact resolve eq30 eq123344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq123626 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq123344 eq122333
    | exact resolve eq122333 eq123344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122333 eq123344
  have eq123627 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq123626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123626
  have eq123898 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq123365
    | exact resolve eq123365 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123365
  have eq123918 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq123898 eq29
    | exact resolve eq29 eq123898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123898
  have eq124224 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq123918
    | exact resolve eq123918 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123918
  have eq124289 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124224 eq214
    | exact resolve eq214 eq124224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125528 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq123627 eq163
    | exact resolve eq163 eq123627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq123627
  have eq125584 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31 eq125528
    | exact resolve eq125528 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125528
  have eq125816 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq124224 eq125584
    | exact resolve eq125584 eq124224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125584
  have eq125878 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq125816
  have eq154247 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq124289 X0
       have i₂ := eq125878
       grind)
    | exact superpose eq125878 eq124289
    | exact resolve eq124289 eq125878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124289 eq125878
  have eq154523 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq154247 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154247
  have eq154597 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq154523 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq154523
    | (have j0 := eq154523 X0
       grind)
    | exact resolve eq154523 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154523
  have eq154602 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124224 eq154597
    | exact resolve eq154597 eq124224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124224 eq154597
  have eq154965 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq154602 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154602
  have eq156260 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq154965 x
       grind)
    | exact superpose eq154965 eq19
    | (have j1 := eq154965 x
       grind)
    | exact resolve eq19 eq154965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154965
  have eq156410 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq156260
  have eq156528 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq156410 eq29
    | exact resolve eq29 eq156410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq156410
  have eq156834 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq156528
    | exact resolve eq156528 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq156528
  have eq156835 : x = (M.op x y) ∨ x = y := by grind
  clear eq156834
  have eq156855 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq156835 eq21
    | exact resolve eq21 eq156835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156903 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq156835 eq214
    | exact resolve eq214 eq156835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq156835
  have eq157309 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq156855
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq156855
    | exact resolve eq156855 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156855
  have eq157759 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq157309 eq27
    | exact resolve eq27 eq157309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157309
  have eq165036 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3342 y x X0
       have i₂ := eq156903 y
       grind)
    | exact superpose eq156903 eq3342
    | exact resolve eq3342 eq156903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342 eq156903
  have eq165378 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq165036 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq165036
    | (have j0 := eq165036 X0
       grind)
    | exact resolve eq165036 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165036
  have eq166575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq165378 eq157759
    | exact resolve eq157759 eq165378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157759 eq165378
  have eq166742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq166575
  have eq166793 : x = y := by
    first
    | (have r₁ := eq166742
       have r₂ := eq28
       grind)
    | exact resolve eq166742 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166742
  have eq166864 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq166793
       grind)
    | exact superpose eq166793 eq19
    | exact resolve eq19 eq166793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq166865 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq166793
       grind)
    | exact superpose eq166793 eq25
    | exact resolve eq25 eq166793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq166793
  have eq167046 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq166865
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq166865
    | exact resolve eq166865 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq166865
  have eq167071 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq167046 eq27
    | exact resolve eq27 eq167046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq167046
  have eq167394 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq167071 eq69
    | exact resolve eq69 eq167071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq167071
  have eq167454 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq167394
       have i₂ := eq166864
       grind)
    | exact superpose eq166864 eq167394
    | exact resolve eq167394 eq166864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166864 eq167394
  have eq167470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq167454 eq15
    | exact resolve eq15 eq167454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167454
  have eq167584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq167470
    | exact resolve eq167470 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq167470
  have eq167615 : False := by grind
  exact eq167615

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation1061 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq18054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq18054
    | exact resolve eq18054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18054
  have eq18066 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq18055
       have r₂ := eq28
       grind)
    | exact resolve eq18055 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18055
  have eq18070 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq18066
    | exact resolve eq18066 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18066
  have eq18075 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq18070 eq82
    | (have r₁ := eq82
       have r₂ := eq18070
       grind)
    | exact resolve eq82 eq18070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq18070
  have eq18105 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq18075
  have eq18106 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq18105
  have eq18286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq18106 eq105
    | exact resolve eq105 eq18106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq18106
  have eq18295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18286
  have eq18298 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18295
       have r₂ := eq28
       grind)
    | exact resolve eq18295 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18295
  have eq18300 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq18298
       grind)
    | exact superpose eq18298 eq52
    | exact resolve eq52 eq18298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq18302 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18298
       grind)
    | exact superpose eq18298 eq81
    | (have r₁ := eq81
       have r₂ := eq18298
       grind)
    | exact resolve eq81 eq18298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq18298
  have eq18331 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq18302
  have eq18332 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18331
  have eq18343 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18300
    | exact resolve eq18300 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18300
  have eq18351 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18332
       grind)
    | exact superpose eq18332 eq90
    | exact resolve eq90 eq18332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq18332
  have eq18367 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18351
    | exact resolve eq18351 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18351
  have eq18605 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18367 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq18367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18367
  have eq18606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18605
  have eq18610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq18606
    | exact resolve eq18606 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18606
  have eq18621 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18610
       have r₂ := eq28
       grind)
    | exact resolve eq18610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18610
  have eq18625 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq18621
    | exact resolve eq18621 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18621
  have eq18638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18625 eq18343
    | exact resolve eq18343 eq18625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18343 eq18625
  have eq18662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18638
  have eq18666 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18662
       have r₂ := eq28
       grind)
    | exact resolve eq18662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18662
  have eq18669 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq18666 eq30
    | exact resolve eq30 eq18666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18666
  have eq18788 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq18669
    | exact resolve eq18669 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18669
  have eq18789 : x = y := by grind
  clear eq18788
  have eq18808 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18789
       grind)
    | exact superpose eq18789 eq19
    | exact resolve eq19 eq18789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18809 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq18789
       grind)
    | exact superpose eq18789 eq25
    | exact resolve eq25 eq18789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18789
  have eq18926 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18809
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18809
    | exact resolve eq18809 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18809
  have eq18941 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18926 eq27
    | exact resolve eq27 eq18926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18926
  have eq19682 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18941 eq69
    | exact resolve eq69 eq18941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq18941
  have eq19721 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19682
       have i₂ := eq18808
       grind)
    | exact superpose eq18808 eq19682
    | exact resolve eq19682 eq18808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18808 eq19682
  have eq19730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19721 eq15
    | exact resolve eq15 eq19721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19721
  have eq19774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19730
    | exact resolve eq19730 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19730
  have eq19783 : False := by grind
  exact eq19783

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1061 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq70 : y ≠ (M.op x y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq833
    | exact resolve eq833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq837 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq834
       have r₂ := eq28
       grind)
    | exact resolve eq834 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq839 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq837
    | exact resolve eq837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq841 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq839 eq71
    | (have r₁ := eq71
       have r₂ := eq839
       grind)
    | exact resolve eq71 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq844 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq839 eq28
    | exact resolve eq28 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq845 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq841
  have eq846 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq845
  have eq914 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq846 eq103
    | exact resolve eq103 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq846
  have eq918 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq914
  have eq923 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq918
       have r₂ := eq844
       grind)
    | exact resolve eq918 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq918
  have eq928 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq923 eq30
    | exact resolve eq30 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq948 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq928
    | exact resolve eq928 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq949 : y = (M.op x y) ∨ x = y := by grind
  clear eq948
  have eq952 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq949 eq21
    | exact resolve eq21 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq949 eq70
    | (have r₁ := eq70
       have r₂ := eq949
       grind)
    | exact resolve eq70 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq949
  have eq964 : y ≠ y ∨ x = y ∨ y = (k y x) := by grind
  clear eq955
  have eq965 : y = (k y x) ∨ x = y := by grind
  clear eq964
  have eq974 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq952
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq952
    | exact resolve eq952 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1010 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq965
       grind)
    | exact superpose eq965 eq88
    | exact resolve eq88 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq965
  have eq1015 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1010
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1010
    | exact resolve eq1010 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1083 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1015 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1084 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1083
  have eq1090 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1084
    | exact resolve eq1084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1158 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1090 eq28
    | exact resolve eq28 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1161 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1158
       have r₂ := eq974
       grind)
    | exact resolve eq1158 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq1158
  have eq1236 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1161 eq30
    | exact resolve eq30 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1161
  have eq1262 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1236
    | exact resolve eq1236 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1236
  have eq1263 : x = y := by grind
  clear eq1262
  have eq1266 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1263
       grind)
    | exact superpose eq1263 eq19
    | exact resolve eq19 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1267 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1263
       grind)
    | exact superpose eq1263 eq25
    | exact resolve eq25 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1263
  have eq1288 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1267
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1267
    | exact resolve eq1267 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1267
  have eq1292 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1288 eq27
    | exact resolve eq27 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1288
  have eq1326 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1292 eq69
    | exact resolve eq69 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1292
  have eq1331 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1326
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq1326
    | exact resolve eq1326 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq1326
  have eq1334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1331 eq15
    | exact resolve eq15 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1334
    | exact resolve eq1334 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1334
  have eq1365 : False := by grind
  exact eq1365
