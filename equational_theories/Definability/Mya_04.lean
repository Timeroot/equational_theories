import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_y_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  clear eq25
  have eq47 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op X0 y))) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X2) (M.op X0 X2)) (M.op (M.op X1 X2) (M.op X0 X2))) = X0 ∨ (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) (M.op X0 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 X2) (M.op X0 X2)) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X0 X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X2)) (M.op (M.op X1 X2) (M.op X0 X2))) = X0 ∨ (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
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
  have eq90 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq521 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq532 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq521 X0
       grind)
    | exact superpose eq521 eq14
    | exact resolve eq14 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) = X0 ∨ (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  clear eq68
  have eq878 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq869 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq885 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq878 X1 X0 (M.op X0 X0)
       have i₂ := eq521 X0
       grind)
    | exact superpose eq521 eq878
    | exact resolve eq878 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq878
  have eq1072 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq532
    | exact resolve eq532 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq1367 : (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq47 eq885
    | exact resolve eq885 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1369 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq48 eq885
    | exact resolve eq885 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq885
  have eq1403 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1367 eq90
    | exact resolve eq90 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1367
  have eq1407 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1403
    | exact resolve eq1403 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1414 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1407 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1415 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1414
  have eq1695 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1415 eq1072
    | exact resolve eq1072 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1698 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1695
  have eq18916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18916
    | exact resolve eq18916 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18916
  have eq18934 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18923
       have r₂ := eq28
       grind)
    | exact resolve eq18923 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18923
  have eq18937 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18934
    | exact resolve eq18934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18934
  have eq19009 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18937 eq1072
    | exact resolve eq1072 eq18937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18937
  have eq19013 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19009
    | exact resolve eq19009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19009
  have eq19014 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19013
  have eq19161 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1072 y y
       have i₂ := eq19014
       grind)
    | exact superpose eq19014 eq1072
    | exact resolve eq1072 eq19014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19014
  have eq19165 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19161
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19161
    | exact resolve eq19161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19161
  have eq19166 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19165
  have eq19168 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19166 eq28
    | exact resolve eq28 eq19166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19214 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19166 eq1369
    | exact resolve eq1369 eq19166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369 eq19166
  have eq20228 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19214 eq101
    | exact resolve eq101 eq19214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq19214
  have eq20245 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq20228
  have eq20255 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20245
       have r₂ := eq19168
       grind)
    | exact resolve eq20245 eq19168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19168 eq20245
  have eq20326 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1072 y y
       have i₂ := eq20255
       grind)
    | exact superpose eq20255 eq1072
    | exact resolve eq1072 eq20255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq20255
  have eq20330 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20326
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20326
    | exact resolve eq20326 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20326
  have eq20331 : x = (M.op x y) := by grind
  clear eq20330
  have eq20333 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20331 eq21
    | exact resolve eq21 eq20331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20331
  have eq20474 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20333
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20333
    | exact resolve eq20333 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20333
  have eq20476 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20474 eq27
    | exact resolve eq27 eq20474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20474
  have eq20622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1698 eq20476
    | exact resolve eq20476 eq1698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698 eq20476
  have eq20632 : False := by grind
  exact eq20632

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_y_y_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq51 : x ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq464 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq649 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq23716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23716
    | exact resolve eq23716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23716
  have eq23737 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23726
       have r₂ := eq28
       grind)
    | exact resolve eq23726 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23726
  have eq23740 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23737
    | exact resolve eq23737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23737
  have eq23746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23740 eq464
    | exact resolve eq464 eq23740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23740
  have eq23799 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23746
    | exact resolve eq23746 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23746
  have eq23800 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23799
  have eq23958 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq464 x
       have i₂ := eq23800
       grind)
    | exact superpose eq23800 eq464
    | exact resolve eq464 eq23800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23959 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71 x
       have i₂ := eq23800
       grind)
    | exact superpose eq23800 eq71
    | exact resolve eq71 eq23800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq23800
  have eq24010 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23959
       have r₂ := eq51
       grind)
    | exact resolve eq23959 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq23959
  have eq24011 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23958
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23958
    | exact resolve eq23958 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23958
  have eq24012 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24011
  have eq24014 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24012 eq28
    | exact resolve eq28 eq24012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24012
  have eq24197 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq24010
       grind)
    | exact superpose eq24010 eq77
    | exact resolve eq77 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq24213 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq649 x y
       have i₂ := eq24010
       grind)
    | exact superpose eq24010 eq649
    | (have j0 := eq649 x y
       grind)
    | exact resolve eq649 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq24010
  have eq24214 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24213
  have eq24217 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24214
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24214
    | exact resolve eq24214 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24214
  have eq24233 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24197
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24197
    | exact resolve eq24197 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24197
  have eq24235 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24217
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24217
    | exact resolve eq24217 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24217
  have eq24244 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq24233
       have r₂ := eq52
       grind)
    | exact resolve eq24233 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq24233
  have eq24245 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24235
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24235
    | exact resolve eq24235 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq24235
  have eq24254 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24245
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24245
    | exact resolve eq24245 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24245
  have eq24263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq24254
    | exact resolve eq24254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24254
  have eq24264 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24263
  have eq24302 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24244 eq102
    | exact resolve eq102 eq24244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq24244
  have eq24329 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24302
       have r₂ := eq24014
       grind)
    | exact resolve eq24302 eq24014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24014 eq24302
  have eq24506 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24264 eq464
    | exact resolve eq464 eq24264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24264
  have eq24558 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq24506
    | exact resolve eq24506 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq24506
  have eq24559 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24558
  have eq24562 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq24559 eq28
    | exact resolve eq28 eq24559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24559
  have eq25230 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq464 x
       have i₂ := eq24329
       grind)
    | exact superpose eq24329 eq464
    | exact resolve eq464 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq24329
  have eq25282 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25230
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25230
    | exact resolve eq25230 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25230
  have eq25283 : x = (M.op x y) := by grind
  clear eq25282
  have eq25285 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25283 eq21
    | exact resolve eq21 eq25283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25283
  have eq25423 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25285
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25285
    | exact resolve eq25285 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25285
  have eq25427 : False := by grind
  exact eq25427

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_y_x_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op X0 y))) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq116 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq157 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq209 : x = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq526 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq517 X0
       grind)
    | exact superpose eq517 eq14
    | exact resolve eq14 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1019 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq47 eq526
    | exact resolve eq526 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1021 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq48 eq526
    | exact resolve eq526 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq526
  have eq9371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9371
    | exact resolve eq9371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9371
  have eq9383 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9372
       have r₂ := eq28
       grind)
    | exact resolve eq9372 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9372
  have eq9385 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9383
    | exact resolve eq9383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9383
  have eq9581 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9385 eq517
    | exact resolve eq517 eq9385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9582 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9385
  have eq9612 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9581
    | exact resolve eq9581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9581
  have eq9617 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9612
  have eq9889 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq9617
       grind)
    | exact superpose eq9617 eq87
    | exact resolve eq87 eq9617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq9617
  have eq9903 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9889
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9889
    | exact resolve eq9889 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9889
  have eq10478 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9903 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9903
  have eq10481 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10478
    | exact resolve eq10478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10478
  have eq10482 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10481
  have eq10494 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10482
    | exact resolve eq10482 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10482
  have eq10495 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10494
  have eq11112 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10495 eq517
    | exact resolve eq517 eq10495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10495
  have eq11149 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11112
    | exact resolve eq11112 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11112
  have eq11150 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11149
  have eq11155 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11150 eq216
    | exact resolve eq216 eq11150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq11176 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11150 eq1021
    | exact resolve eq1021 eq11150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq11150
  have eq11516 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11176 eq11155
    | exact resolve eq11155 eq11176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11155 eq11176
  have eq11556 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11516
  have eq11560 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11556
    | exact resolve eq11556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11556
  have eq11561 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11560
  have eq12291 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11561 eq28
    | exact resolve eq28 eq11561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18003 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9582 eq100
    | exact resolve eq100 eq9582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9582
  have eq18018 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18003
  have eq18026 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18018
       have r₂ := eq12291
       grind)
    | exact resolve eq18018 eq12291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq18034 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq517 x
       have i₂ := eq18026
       grind)
    | exact superpose eq18026 eq517
    | exact resolve eq517 eq18026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18026
  have eq18071 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18034
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18034
    | exact resolve eq18034 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18034
  have eq18108 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18071 eq11561
    | exact resolve eq11561 eq18071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11561
  have eq18119 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18108
  have eq18151 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18119 eq27
    | exact resolve eq27 eq18119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18152 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18119 eq30
    | exact resolve eq30 eq18119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18119
  have eq18314 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq18152
    | exact resolve eq18152 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18152
  have eq18413 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18314 eq1019
    | exact resolve eq1019 eq18314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20615 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18151
  have eq22642 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18413
  have eq23027 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18071 eq20615
    | exact resolve eq20615 eq18071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18071 eq20615
  have eq23045 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23027
  have eq23731 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq22642
       grind)
    | exact superpose eq22642 eq88
    | exact resolve eq88 eq22642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq22642
  have eq23784 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23731
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23731
    | exact resolve eq23731 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23731
  have eq23811 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23045 eq100
    | exact resolve eq100 eq23045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq23045
  have eq23828 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq23811
  have eq23839 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23828
       have r₂ := eq12291
       grind)
    | exact resolve eq23828 eq12291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23828
  have eq24675 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq517 x
       have i₂ := eq23839
       grind)
    | exact superpose eq23839 eq517
    | exact resolve eq517 eq23839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq23839
  have eq24726 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24675
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24675
    | exact resolve eq24675 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24675
  have eq24727 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24726
  have eq24728 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24727 eq21
    | exact resolve eq21 eq24727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24813 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq24727
  have eq24880 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24728
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24728
    | exact resolve eq24728 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24728
  have eq25124 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24880 eq23784
    | exact resolve eq23784 eq24880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23784 eq24880
  have eq25125 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq25124
  have eq25143 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25125
       have r₂ := eq24813
       grind)
    | exact resolve eq25125 eq24813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25125
  have eq25580 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25143 eq157
    | exact resolve eq157 eq25143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq25143
  have eq25633 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq25580
    | exact resolve eq25580 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq25580
  have eq26130 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25633 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq25633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25633
  have eq26150 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq26130
  have eq26384 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26150 eq209
    | exact resolve eq209 eq26150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq26150
  have eq26529 : x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18314 eq26384
    | exact resolve eq26384 eq18314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18314 eq26384
  have eq26580 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26529
  have eq26581 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26580
       have r₂ := eq24813
       grind)
    | exact resolve eq26580 eq24813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24813 eq26580
  have eq26583 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26581
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26581
    | exact resolve eq26581 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq26581
  have eq26584 : x = (M.op x y) := by grind
  clear eq26583
  have eq26589 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq26584 eq21
    | exact resolve eq21 eq26584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26727 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26589
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26589
    | exact resolve eq26589 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26589
  have eq26729 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26727 eq27
    | exact resolve eq27 eq26727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq26815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26727 eq12291
    | (have r₁ := eq12291
       have r₂ := eq26727
       grind)
    | exact resolve eq12291 eq26727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12291
  have eq26834 : y = (M.op x y) := by grind
  clear eq26815
  have eq26843 : x = y := by
    first
    | exact superpose eq26584 eq26834
    | exact resolve eq26834 eq26584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26834
  have eq26908 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq26843
       grind)
    | exact superpose eq26843 eq25
    | exact resolve eq25 eq26843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq26980 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1019
       have i₂ := eq26843
       grind)
    | exact superpose eq26843 eq1019
    | exact resolve eq1019 eq26843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq26843
  have eq27002 : x = (M.op x x) := by
    first
    | exact superpose eq26584 eq26980
    | exact resolve eq26980 eq26584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26584 eq26980
  have eq27073 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26908
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26908
    | exact resolve eq26908 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26908
  have eq27139 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26727 eq27073
    | exact resolve eq27073 eq26727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27073
  have eq27445 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27139 eq26729
    | exact resolve eq26729 eq27139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26729 eq27139
  have eq27511 : x = (k x x) := by grind
  clear eq27002
  have eq27754 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq707 x x
       have i₂ := eq27511
       grind)
    | exact superpose eq27511 eq707
    | (have j0 := eq707 x x
       grind)
    | exact resolve eq707 eq27511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq27511
  have eq27759 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27754
  have eq27760 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27759
  have eq27775 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq27760
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27760
    | exact resolve eq27760 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27760
  have eq27793 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26727 eq27775
    | exact resolve eq27775 eq26727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26727 eq27775
  have eq27811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27445 eq27793
    | exact resolve eq27793 eq27445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27445 eq27793
  have eq27828 : False := by grind
  exact eq27828

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq85 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq96
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq371 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq522 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq8631
    | exact resolve eq8631 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8631
  have eq8643 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8632
       have r₂ := eq29
       grind)
    | exact resolve eq8632 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8632
  have eq8647 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq8643 eq371
    | exact resolve eq371 eq8643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8648 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq8643
  have eq8665 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq8647
    | exact resolve eq8647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8647
  have eq8863 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8665
  have eq9099 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq8863
       grind)
    | exact superpose eq8863 eq85
    | exact resolve eq85 eq8863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq8863
  have eq9115 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9099
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9099
    | exact resolve eq9099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9099
  have eq9375 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9115 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq9115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9115
  have eq9376 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9375
  have eq9380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq9376
    | exact resolve eq9376 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9376
  have eq9381 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq9380
  have eq9424 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq9381 eq371
    | exact resolve eq371 eq9381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq9448 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq9424
    | exact resolve eq9424 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9424
  have eq9449 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9448
  have eq9645 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9449 eq29
    | exact resolve eq29 eq9449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9449
  have eq10399 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq8648 eq97
    | exact resolve eq97 eq8648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq8648
  have eq10408 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq10399
  have eq10417 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10408
       have r₂ := eq9645
       grind)
    | exact resolve eq10408 eq9645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10408
  have eq10425 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq371 x
       have i₂ := eq10417
       grind)
    | exact superpose eq10417 eq371
    | exact resolve eq371 eq10417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq10417
  have eq10458 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10425
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq10425
    | exact resolve eq10425 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10425
  have eq10461 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10458 eq31
    | exact resolve eq31 eq10458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10458
  have eq10582 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq10461
    | exact resolve eq10461 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10461
  have eq10583 : x = (M.op x y) ∨ x = y := by grind
  clear eq10582
  have eq10806 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10583 eq22
    | exact resolve eq22 eq10583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10934 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq10806
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10806
    | exact resolve eq10806 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10806
  have eq11017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10934 eq9645
    | (have r₁ := eq9645
       have r₂ := eq10934
       grind)
    | exact resolve eq9645 eq10934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9645 eq10934
  have eq11024 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq11017
  have eq11025 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq11024
  have eq11085 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq11025 eq31
    | exact resolve eq31 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11025
  have eq11215 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq11085
    | exact resolve eq11085 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq11085
  have eq11460 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq11215 eq10583
    | exact resolve eq10583 eq11215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10583 eq11215
  have eq11461 : x = y := by grind
  clear eq11460
  have eq11525 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq11461
       grind)
    | exact superpose eq11461 eq20
    | exact resolve eq20 eq11461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq11526 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11461
       grind)
    | exact superpose eq11461 eq26
    | exact resolve eq26 eq11461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11461
  have eq11644 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11526
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11526
    | exact resolve eq11526 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11526
  have eq11867 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11644 eq28
    | exact resolve eq28 eq11644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11644
  have eq11997 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11525
       grind)
    | exact superpose eq11525 eq68
    | exact resolve eq68 eq11525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq12001 : x = (k (M.op x y) x) := by grind
  clear eq11525
  have eq12034 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq11997
    | exact resolve eq11997 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11997
  have eq12407 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq20268 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq20280 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11867 eq20268
    | exact resolve eq20268 eq11867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268
  have eq20292 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20280
       have r₂ := eq29
       grind)
    | exact resolve eq20280 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20280
  have eq20297 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11867 eq20292
    | exact resolve eq20292 eq11867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20292
  have eq20301 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20297 eq29
    | exact resolve eq29 eq20297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20330 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20297 eq12407
    | exact resolve eq12407 eq20297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12407 eq20297
  have eq22118 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20330 eq12034
    | exact resolve eq12034 eq20330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034 eq20330
  have eq22133 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22118
  have eq22146 : x = (M.op x y) := by
    first
    | (have r₁ := eq22133
       have r₂ := eq20301
       grind)
    | exact resolve eq22133 eq20301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20301 eq22133
  have eq23844 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22146 eq22
    | exact resolve eq22 eq22146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq23924 : x = (k x x) := by
    first
    | exact superpose eq22146 eq12001
    | exact resolve eq12001 eq22146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12001 eq22146
  have eq23995 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23844
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23844
    | exact resolve eq23844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23844
  have eq24906 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq522 x
       have i₂ := eq23924
       grind)
    | exact superpose eq23924 eq522
    | (have j0 := eq522 x
       grind)
    | exact resolve eq522 eq23924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq23924
  have eq24911 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24906
  have eq24920 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24911
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24911
    | exact resolve eq24911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24911
  have eq24937 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11867 eq24920
    | exact resolve eq24920 eq11867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11867 eq24920
  have eq24952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23995 eq24937
    | exact resolve eq24937 eq23995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23995 eq24937
  have eq24967 : False := by grind
  exact eq24967

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation854 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq107 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq220 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq230 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq9
    | exact resolve eq9 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq281 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq230
    | exact resolve eq230 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq230 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq107 X0 (σ X0)
       grind)
    | exact superpose eq107 eq230
    | exact resolve eq230 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq230
  have eq1987 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq14748 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq193 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193
    | exact resolve eq193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq15030 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14748 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14748
    | (have j0 := eq14748 X0 X1
       grind)
    | exact resolve eq14748 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14748
  have eq20416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1987
       have i₂ := eq15030 x y
       grind)
    | exact superpose eq15030 eq1987
    | (have j1 := eq15030 x y
       grind)
    | (have r₁ := eq1987
       have r₂ := eq15030 x y
       grind)
    | (have r₁ := eq1987
       have r₂ := eq15030 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1987
       have r₂ := eq15030 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1987 eq15030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987 eq15030
  have eq20417 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq20416
  have eq22947 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20417
       grind)
    | exact superpose eq20417 eq16
    | exact resolve eq16 eq20417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20417
  have eq22948 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq22947
       have r₂ := eq23 x
       grind)
    | exact resolve eq22947 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22947
  have eq22950 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22948
       grind)
    | exact superpose eq22948 eq10
    | exact resolve eq10 eq22948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22948
  have eq23036 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22950
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22950
    | exact resolve eq22950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22950
  have eq23038 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23036
       grind)
    | exact superpose eq23036 eq16
    | exact resolve eq16 eq23036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23036
  have eq23039 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23038
       have r₂ := eq23 x
       grind)
    | exact resolve eq23038 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23038
  have eq23076 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq23039
       grind)
    | exact superpose eq23039 eq10
    | exact resolve eq10 eq23039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23039
  have eq23162 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23076
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23076
    | exact resolve eq23076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23076
  have eq23163 : x = (M.op y y) := by grind
  clear eq23162
  have eq23213 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq282 y
       have i₂ := eq23163
       grind)
    | exact superpose eq23163 eq282
    | exact resolve eq282 eq23163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq23316 : x = (M.op x y) := by
    first
    | (have i₁ := eq281 y y
       have i₂ := eq23163
       grind)
    | exact superpose eq23163 eq281
    | exact resolve eq281 eq23163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq23163
  have eq23831 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23213
       grind)
    | exact superpose eq23213 eq16
    | exact resolve eq16 eq23213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23213
  have eq23918 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq23831
       have i₂ := eq23316
       grind)
    | exact superpose eq23316 eq23831
    | exact resolve eq23831 eq23316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23316 eq23831
  have eq23919 : False := by grind
  exact eq23919
