import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxx_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq249 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq249 X0
       grind)
    | exact superpose eq249 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq249 X0
       grind)
    | exact resolve eq13 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq397 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq463 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
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
  clear eq53
  have eq768 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq3454 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq463
    | exact resolve eq463 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq463
  have eq3485 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3454 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3454
    | (have j0 := eq3454 y x
       grind)
    | exact resolve eq3454 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3487 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3454
    | (have j0 := eq3454 (σ y) (σ x)
       grind)
    | exact resolve eq3454 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454
  have eq14946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14946
    | exact resolve eq14946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14946
  have eq14964 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14953
       have r₂ := eq28
       grind)
    | exact resolve eq14953 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14953
  have eq14966 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14964
    | exact resolve eq14964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14964
  have eq14978 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14966 eq54
    | exact resolve eq54 eq14966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14966
  have eq15004 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14978
    | exact resolve eq14978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14978
  have eq15005 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15004
  have eq15016 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq15005
       grind)
    | exact superpose eq15005 eq54
    | exact resolve eq54 eq15005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15005
  have eq15040 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15016
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15016
    | exact resolve eq15016 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15016
  have eq15041 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15040
  have eq15042 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15041 eq28
    | exact resolve eq28 eq15041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15054 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15041 eq3487
    | exact resolve eq3487 eq15041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3487
  have eq15065 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq15054
    | exact resolve eq15054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15054
  have eq15229 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15065 eq397
    | exact resolve eq397 eq15065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15065
  have eq15468 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15041 eq15229
    | exact resolve eq15229 eq15041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15041 eq15229
  have eq15481 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15468
  have eq16155 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15481 eq109
    | exact resolve eq109 eq15481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq15481
  have eq16172 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq16155
  have eq16181 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16172
       have r₂ := eq15042
       grind)
    | exact resolve eq16172 eq15042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15042 eq16172
  have eq16348 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq16181
       grind)
    | exact superpose eq16181 eq54
    | exact resolve eq54 eq16181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16181
  have eq16372 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16348
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16348
    | exact resolve eq16348 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16348
  have eq16373 : x = (M.op x y) := by grind
  clear eq16372
  have eq16374 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16373 eq21
    | exact resolve eq21 eq16373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq16436 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq16373 eq3485
    | exact resolve eq3485 eq16373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3485
  have eq16449 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16436
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16436
    | exact resolve eq16436 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16436
  have eq16500 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16374
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16374
    | exact resolve eq16374 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16374
  have eq16501 : x = (M.op y y) := by
    first
    | exact superpose eq16373 eq16449
    | exact resolve eq16449 eq16373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16373 eq16449
  have eq16554 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16500 eq27
    | exact resolve eq27 eq16500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16726 : x = (k y x) := by
    first
    | (have i₁ := eq397 y
       have i₂ := eq16501
       grind)
    | exact superpose eq16501 eq397
    | exact resolve eq397 eq16501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq16501
  have eq16820 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq768 x y
       have i₂ := eq16726
       grind)
    | exact superpose eq16726 eq768
    | (have j0 := eq768 x y
       grind)
    | exact resolve eq768 eq16726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq16726
  have eq16823 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16820
  have eq16827 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16823
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16823
    | exact resolve eq16823 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16823
  have eq16839 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16500 eq16827
    | exact resolve eq16827 eq16500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16827
  have eq16849 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16839
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16839
    | exact resolve eq16839 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16839
  have eq16859 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16849
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16849
    | exact resolve eq16849 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16849
  have eq16865 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16859
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16859
    | exact resolve eq16859 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16859
  have eq16868 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq16865
    | exact resolve eq16865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16865
  have eq16870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16500 eq16868
    | exact resolve eq16868 eq16500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16500 eq16868
  have eq16872 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq16870
       have r₂ := eq28
       grind)
    | exact resolve eq16870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16870
  have eq17046 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16872 eq54
    | exact resolve eq54 eq16872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq16872
  have eq17072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16554 eq17046
    | exact resolve eq17046 eq16554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16554 eq17046
  have eq17076 : False := by grind
  exact eq17076

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq10
    | exact resolve eq10 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq73 (τ X0)
       grind)
    | exact superpose eq73 eq35
    | exact resolve eq35 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq310 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq299
    | exact resolve eq299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq312 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq310 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq310
    | exact resolve eq310 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq310
  have eq437 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq54
    | exact resolve eq54 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq538 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
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
  clear eq53
  have eq637 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq16
    | exact resolve eq16 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq841 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq437 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq437
    | exact resolve eq437 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq988 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq277 (τ X0)
       have i₂ := eq637 X0
       grind)
    | exact superpose eq637 eq277
    | exact resolve eq277 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq637
  have eq3692 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq538
    | exact resolve eq538 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq538
  have eq3735 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3692 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3692
    | (have j0 := eq3692 y x
       grind)
    | exact resolve eq3692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq13377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq13376
    | exact resolve eq13376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13376
  have eq13388 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq13377
       have r₂ := eq28
       grind)
    | exact resolve eq13377 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13377
  have eq13412 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq13388 eq3692
    | exact resolve eq3692 eq13388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13722 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq13412 eq13388
    | exact resolve eq13388 eq13412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388 eq13412
  have eq13744 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq13722
  have eq13778 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq13744 eq988
    | exact resolve eq988 eq13744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq13744
  have eq13797 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq13778
    | exact resolve eq13778 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13778
  have eq13807 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq13797
    | exact resolve eq13797 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13797
  have eq13808 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13807
  have eq13835 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3692 x y
       have i₂ := eq13808
       grind)
    | exact superpose eq13808 eq3692
    | exact resolve eq3692 eq13808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692
  have eq14049 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13808
       have i₂ := eq13835
       grind)
    | exact superpose eq13835 eq13808
    | exact resolve eq13808 eq13835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13808 eq13835
  have eq14071 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14049
  have eq14197 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq14071
       grind)
    | exact superpose eq14071 eq54
    | exact resolve eq54 eq14071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq14071
  have eq14243 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14197
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14197
    | exact resolve eq14197 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14197
  have eq14267 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14243 eq30
    | exact resolve eq30 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14243
  have eq14379 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq14267
    | exact resolve eq14267 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14267
  have eq14380 : x = (M.op x y) ∨ x = y := by grind
  clear eq14379
  have eq14408 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14380 eq21
    | exact resolve eq21 eq14380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14467 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq14380 eq3735
    | exact resolve eq3735 eq14380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735 eq14380
  have eq14480 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14467
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14467
    | exact resolve eq14467 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14467
  have eq14528 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14408
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14408
    | exact resolve eq14408 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14408
  have eq14671 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq14528 eq27
    | exact resolve eq27 eq14528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14528
  have eq14848 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq841 y
       have i₂ := eq14480
       grind)
    | exact superpose eq14480 eq841
    | exact resolve eq841 eq14480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq14480
  have eq14874 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14848
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14848
    | exact resolve eq14848 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14848
  have eq14890 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq14874
    | exact resolve eq14874 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14874
  have eq15543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14890 eq14671
    | exact resolve eq14671 eq14890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14671 eq14890
  have eq15562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq15543
  have eq15565 : x = y := by
    first
    | (have r₁ := eq15562
       have r₂ := eq28
       grind)
    | exact resolve eq15562 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15562
  have eq15677 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15565
       grind)
    | exact superpose eq15565 eq19
    | exact resolve eq19 eq15565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15678 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15565
       grind)
    | exact superpose eq15565 eq25
    | exact resolve eq25 eq15565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15565
  have eq15781 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15678
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15678
    | exact resolve eq15678 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15678
  have eq15808 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15781 eq27
    | exact resolve eq27 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15781
  have eq16084 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15808 eq78
    | exact resolve eq78 eq15808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq15808
  have eq16146 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16084
       have i₂ := eq15677
       grind)
    | exact superpose eq15677 eq16084
    | exact resolve eq16084 eq15677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15677 eq16084
  have eq16156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16146 eq15
    | exact resolve eq15 eq16146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16146
  have eq16201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16156
    | exact resolve eq16156 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16156
  have eq16208 : False := by grind
  exact eq16208

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
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
  have eq5130 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq2703 eq181
    | exact resolve eq181 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq2703
  have eq5136 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq1258 eq5130
    | exact resolve eq5130 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5130
  have eq5156 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq5136
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq5136
    | exact resolve eq5136 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5136
  have eq5161 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5156
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq5156
    | exact resolve eq5156 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq5172 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5161 eq28
    | (have j0 := eq28 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq28 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq5179 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3149 eq5172
    | exact resolve eq5172 eq3149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149 eq5172
  have eq5180 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq5179
  have eq5184 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1258 eq5180
    | exact resolve eq5180 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq5180
  have eq5186 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5184
       have i₂ := eq3108
       grind)
    | exact superpose eq3108 eq5184
    | exact resolve eq5184 eq3108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108 eq5184
  have eq5195 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5186 eq178
    | exact resolve eq178 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq5186
  have eq5224 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5161 eq5195
    | exact resolve eq5195 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161 eq5195
  have eq5225 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq5224
  have eq5240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5225 eq14
    | exact resolve eq14 eq5225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5225
  have eq5252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5240
    | exact resolve eq5240 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5240
  have eq5256 : False := by grind
  exact eq5256

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq44
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq84 (σ X0)
       grind)
    | exact superpose eq84 eq31
    | exact resolve eq31 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq92 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq84 (τ X0)
       grind)
    | exact superpose eq84 eq18
    | exact resolve eq18 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq93 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq93
    | exact resolve eq93 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq95
    | exact resolve eq95 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq95
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq101 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq137 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq306 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq25
    | exact resolve eq25 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq137
       have i₂ := eq120 x
       grind)
    | exact superpose eq120 eq137
    | exact resolve eq137 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq518 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq517
       have i₂ := eq120 y
       grind)
    | exact superpose eq120 eq517
    | exact resolve eq517 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq519 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq518
       have i₂ := eq120 x
       grind)
    | exact superpose eq120 eq518
    | exact resolve eq518 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq547 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq519
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq519
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq519 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq548 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq547
  have eq8143 : (M.op x x) = (τ (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq548
       grind)
    | exact superpose eq548 eq10
    | exact resolve eq10 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq8206 : y = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8143
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8143
    | exact resolve eq8143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8143
  have eq8207 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) := by grind
  clear eq8206
  have eq246812 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76 y y
       have i₂ := eq8207
       grind)
    | exact superpose eq8207 eq76
    | exact resolve eq76 eq8207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207
  have eq247035 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq246812
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq246812
    | exact resolve eq246812 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246812
  have eq247068 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247035
       grind)
    | exact superpose eq247035 eq16
    | exact resolve eq16 eq247035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247035
  have eq247069 : y = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq247068
       have r₂ := eq120 x
       grind)
    | exact resolve eq247068 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247068
  have eq247949 : x = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq25 x
       have i₂ := eq247069
       grind)
    | exact superpose eq247069 eq25
    | exact resolve eq25 eq247069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq247955 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq306 x
       have i₂ := eq247069
       grind)
    | exact superpose eq247069 eq306
    | exact resolve eq306 eq247069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq247069
  have eq357700 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247955
       grind)
    | exact superpose eq247955 eq16
    | exact resolve eq16 eq247955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247955
  have eq359316 : (σ x) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq357700
       have i₂ := eq247949
       grind)
    | exact superpose eq247949 eq357700
    | exact resolve eq357700 eq247949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247949 eq357700
  have eq359317 : (σ x) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq359316
  have eq359318 : (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq359317
  have eq359420 : (τ (M.op (σ (M.op x x)) (σ (M.op x x)))) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq102 (M.op y y)
       have i₂ := eq359318
       grind)
    | exact superpose eq359318 eq102
    | exact resolve eq102 eq359318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359318
  have eq359897 : y = (τ (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq359420
       have i₂ := eq76 y y
       grind)
    | exact superpose eq76 eq359420
    | exact resolve eq359420 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359420
  have eq360007 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq359897
       have i₂ := eq102 (M.op x x)
       grind)
    | exact superpose eq102 eq359897
    | exact resolve eq359897 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq359897
  have eq360024 : x = y := by
    first
    | (have i₁ := eq360007
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq360007
    | exact resolve eq360007 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq360007
  have eq360032 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq360024
       grind)
    | exact superpose eq360024 eq16
    | exact resolve eq16 eq360024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360024
  have eq360033 : False := by grind
  exact eq360033

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq66 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq67 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq66
    | exact resolve eq66 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : y = (M.op (M.op x y) (M.op y y)) := by
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
  have eq327 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq77
    | (have j0 := eq77 (σ X0)
       grind)
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq44
    | (have j1 := eq77 x
       grind)
    | exact resolve eq44 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 X0) X0 X1 X2
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
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
  have eq381 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
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
  have eq3282 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq378
    | exact resolve eq378 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq3309 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3282 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3282
    | (have j0 := eq3282 y x
       grind)
    | exact resolve eq3282 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3311 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3282
    | (have j0 := eq3282 (σ y) (σ x)
       grind)
    | exact resolve eq3282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282
  have eq3578 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq50
    | (have j1 := eq327 X0
       grind)
    | exact resolve eq50 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3590 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq3948 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq381 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq381
    | exact resolve eq381 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq6066 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1 (M.op X0 X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq367
    | exact resolve eq367 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq18278 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3948 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq3948
    | exact resolve eq3948 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3948
  have eq18907 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq6066 X1 X0
       grind)
    | exact superpose eq6066 eq14
    | exact resolve eq14 eq6066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6066
  have eq26577 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3590 x
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3590
    | (have j0 := eq3590 x
       grind)
    | exact resolve eq3590 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq26582 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26577
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26577
    | exact resolve eq26577 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26577
  have eq26589 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26582
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26582
    | exact resolve eq26582 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26582
  have eq33378 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq52
    | exact resolve eq52 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq33419 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33378
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq33378
    | exact resolve eq33378 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33378
  have eq33436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq33419 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq33419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq33436
    | exact resolve eq33436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33436
  have eq33448 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq33437
       have r₂ := eq28
       grind)
    | exact resolve eq33437 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33437
  have eq33514 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq33448 eq18907
    | exact resolve eq18907 eq33448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18907 eq33448
  have eq33525 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33514 x
       have i₂ := eq14 sF2 x sF2
       grind)
    | exact superpose eq14 eq33514
    | exact resolve eq33514 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33514
  have eq33606 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq33525 eq18278
    | exact resolve eq18278 eq33525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33525
  have eq33621 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq33606
    | exact resolve eq33606 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33606
  have eq33733 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq33621
       grind)
    | exact superpose eq33621 eq52
    | exact resolve eq52 eq33621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq33750 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18278 y y
       have i₂ := eq33621
       grind)
    | exact superpose eq33621 eq18278
    | exact resolve eq18278 eq33621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33621
  have eq33765 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33750
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33750
    | exact resolve eq33750 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33750
  have eq33790 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq33765 eq28
    | exact resolve eq28 eq33765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33799 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq33765 eq3311
    | exact resolve eq3311 eq33765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq33868 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq33799
    | exact resolve eq33799 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33799
  have eq34805 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq331
       have i₂ := eq33733
       grind)
    | exact superpose eq33733 eq331
    | exact resolve eq331 eq33733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33733
  have eq34862 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34805
  have eq34869 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34862
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34862
    | exact resolve eq34862 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34862
  have eq35094 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq33868
  have eq35224 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34869 eq56
    | exact resolve eq56 eq34869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq34869
  have eq35245 : y = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq35224
    | exact resolve eq35224 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35224
  have eq35277 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq33765 eq35094
    | exact resolve eq35094 eq33765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33765 eq35094
  have eq35280 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq35277
  have eq35426 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq35280 eq33419
    | exact resolve eq33419 eq35280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33419 eq35280
  have eq35428 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq35426
  have eq35431 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35428
       have r₂ := eq33790
       grind)
    | exact resolve eq35428 eq33790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33790 eq35428
  have eq35595 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18278 y y
       have i₂ := eq35431
       grind)
    | exact superpose eq35431 eq18278
    | exact resolve eq18278 eq35431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18278 eq35431
  have eq35610 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35595
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35595
    | exact resolve eq35595 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35595
  have eq35611 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq35610
  have eq35640 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq35611 eq30
    | exact resolve eq30 eq35611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35611
  have eq35838 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq35640
    | exact resolve eq35640 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35640
  have eq35839 : x = (M.op x y) ∨ x = y := by grind
  clear eq35838
  have eq35840 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq35839 eq21
    | exact resolve eq21 eq35839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35886 : y = (M.op x (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq35839 eq225
    | exact resolve eq225 eq35839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq35908 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq35839 eq3309
    | exact resolve eq3309 eq35839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq35985 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq35908
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35908
    | exact resolve eq35908 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35908
  have eq36046 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq35840
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35840
    | exact resolve eq35840 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35840
  have eq37603 : y = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35886
       have i₂ := eq35985
       grind)
    | exact superpose eq35985 eq35886
    | exact resolve eq35886 eq35985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35886 eq35985
  have eq37661 : y = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq37603
  have eq37675 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq35839 eq37661
    | exact resolve eq37661 eq35839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37661
  have eq37721 : y = (M.op x x) ∨ x = y := by grind
  clear eq37675
  have eq37728 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq331
       have i₂ := eq37721
       grind)
    | exact superpose eq37721 eq331
    | exact resolve eq331 eq37721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37721
  have eq37788 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq37728
  have eq37794 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37788
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37788
    | exact resolve eq37788 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37788
  have eq38084 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36046 eq37794
    | exact resolve eq37794 eq36046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38097 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq37794 eq26589
    | exact resolve eq26589 eq37794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26589 eq37794
  have eq38103 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq38084
  have eq90576 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3578 x
       have i₂ := eq35245
       grind)
    | exact superpose eq35245 eq3578
    | (have j0 := eq3578 x
       grind)
    | exact resolve eq3578 eq35245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578 eq35245
  have eq90669 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90576
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90576
    | exact resolve eq90576 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90576
  have eq90699 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90669
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq90669
    | exact resolve eq90669 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90669
  have eq90718 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq90699
    | exact resolve eq90699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90699
  have eq90719 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq90718
  have eq90728 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq90719
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq90719
    | exact resolve eq90719 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90719
  have eq90732 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq90728
       have r₂ := eq38097
       grind)
    | exact resolve eq90728 eq38097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38097 eq90728
  have eq90734 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36046 eq90732
    | exact resolve eq90732 eq36046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36046 eq90732
  have eq90803 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq90734
  have eq90818 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq90803
       have r₂ := eq28
       grind)
    | exact resolve eq90803 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90803
  have eq90829 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq90818
  have eq90906 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq90829 eq38103
    | exact resolve eq38103 eq90829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38103 eq90829
  have eq90919 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq90906
  have eq91110 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq90919 eq30
    | exact resolve eq30 eq90919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq90919
  have eq91453 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq91110
    | exact resolve eq91110 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq91110
  have eq91654 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq91453 eq35839
    | exact resolve eq35839 eq91453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35839 eq91453
  have eq91838 : x = y := by grind
  clear eq91654
  have eq92044 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq91838
       grind)
    | exact superpose eq91838 eq19
    | exact resolve eq19 eq91838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq92045 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq91838
       grind)
    | exact superpose eq91838 eq25
    | exact resolve eq25 eq91838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq91838
  have eq92361 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq92045
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq92045
    | exact resolve eq92045 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92045
  have eq92365 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq92361 eq27
    | exact resolve eq27 eq92361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq92361
  have eq92643 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq331
       have i₂ := eq92044
       grind)
    | exact superpose eq92044 eq331
    | exact resolve eq331 eq92044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq92685 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq92044
  have eq92750 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq92643
    | exact resolve eq92643 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92643
  have eq92788 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq105281 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92750 eq77
    | (have j0 := eq77 (σ x)
       grind)
    | exact resolve eq77 eq92750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq105282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92365 eq105281
    | exact resolve eq105281 eq92365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105281
  have eq105296 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq105282
       have r₂ := eq28
       grind)
    | exact resolve eq105282 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105282
  have eq105303 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92365 eq105296
    | exact resolve eq105296 eq92365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105296
  have eq106314 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105303 eq28
    | exact resolve eq28 eq105303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106397 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105303 eq92788
    | exact resolve eq92788 eq105303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92788 eq105303
  have eq107585 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106397 eq92750
    | exact resolve eq92750 eq106397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92750 eq106397
  have eq107601 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq107585
  have eq107610 : x = (M.op x y) := by
    first
    | (have r₁ := eq107601
       have r₂ := eq106314
       grind)
    | exact resolve eq107601 eq106314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106314 eq107601
  have eq107632 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq107610 eq21
    | exact resolve eq21 eq107610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq107906 : x = (k x x) := by
    first
    | exact superpose eq107610 eq92685
    | exact resolve eq92685 eq107610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92685 eq107610
  have eq108100 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq107632
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq107632
    | exact resolve eq107632 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107632
  have eq108669 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3590 x
       have i₂ := eq107906
       grind)
    | exact superpose eq107906 eq3590
    | (have j0 := eq3590 x
       grind)
    | exact resolve eq3590 eq107906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590 eq107906
  have eq108673 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq108669
  have eq108685 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq108673
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq108673
    | exact resolve eq108673 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq108673
  have eq108703 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92365 eq108685
    | exact resolve eq108685 eq92365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92365 eq108685
  have eq108719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108100 eq108703
    | exact resolve eq108703 eq108100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108100 eq108703
  have eq108734 : False := by grind
  exact eq108734

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq9
    | exact resolve eq9 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq45 (σ X0)
       grind)
    | exact superpose eq45 eq31
    | exact resolve eq31 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq92 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq162 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X2 (M.op X0 X1) X1
       have i₂ := eq37 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq37 eq34
    | exact resolve eq34 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq34 X1 X4 X0 X2
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49 x y
       grind)
    | exact superpose eq49 eq16
    | (have j1 := eq49 x y
       grind)
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq49 X0 X0
       grind)
    | exact superpose eq49 eq37
    | (have j1 := eq49 X0 X0
       grind)
    | exact resolve eq37 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq227 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq249 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq34 X1 X1 X0 X2
       grind)
    | exact superpose eq34 eq44
    | exact resolve eq44 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq343 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq249 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq35 (M.op X0 X1)
       grind)
    | exact superpose eq35 eq249
    | exact resolve eq249 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq370 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq343 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq343
    | exact resolve eq343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq343 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq343
    | exact resolve eq343 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X3 X1)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq343 (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq34 X1 X3 X0 X2
       grind)
    | exact superpose eq34 eq343
    | exact resolve eq343 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq370 X0 X1 X2
       have i₂ := eq371 (M.op X0 X2) X1
       grind)
    | exact superpose eq371 eq370
    | exact resolve eq370 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq587 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X1 X0)
       have i₂ := eq371 X0 X1
       grind)
    | exact superpose eq371 eq35
    | exact resolve eq35 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq395 X1 X0 X0
       grind)
    | exact superpose eq395 eq587
    | exact resolve eq587 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq587
  have eq1250 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq167 X1 X0 X1 X0 X2
       have i₂ := eq611 X1 X0
       grind)
    | exact superpose eq611 eq167
    | exact resolve eq167 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq1340 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1250 X0 X1 X2
       have i₂ := eq371 X0 X2
       grind)
    | exact superpose eq371 eq1250
    | exact resolve eq1250 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1526 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1340 X0 (M.op X0 X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq1340
    | exact resolve eq1340 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1569 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X2 X1 X1
       have i₂ := eq1340 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq1340 eq34
    | exact resolve eq34 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1340
  have eq2302 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1526 X2 X1
       have i₂ := eq1569 X1 X2 X0
       grind)
    | (have i₁ := eq1526 (M.op X2 X0) X0
       have i₂ := eq1569 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1569 eq1526
    | exact resolve eq1526 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq1569
  have eq3651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq205
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq205
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq205 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq3652 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq3651
  have eq17848 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq227 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227
    | exact resolve eq227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17863 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0
       have i₂ := eq227 X0 X1
       grind)
    | exact superpose eq227 eq92
    | (have j1 := eq227 X0 X1
       grind)
    | exact resolve eq92 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq17996 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17863 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17863
    | (have j0 := eq17863 X0 X1
       grind)
    | exact resolve eq17863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17863
  have eq18006 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17848 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq17848
    | (have j0 := eq17848 X0 X1
       grind)
    | exact resolve eq17848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17848
  have eq18012 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18006 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18006
    | (have j0 := eq18006 X0 X1
       grind)
    | exact resolve eq18006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18006
  have eq18094 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq343 (k X0 X0) X0
       have i₂ := eq18012 X0 (k X0 X0)
       grind)
    | exact superpose eq18012 eq343
    | (have j1 := eq18012 X0 x
       grind)
    | exact resolve eq343 eq18012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18012
  have eq18332 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 (k X0 X0) (k X0 X0)
       have i₂ := eq18094 X0
       grind)
    | exact superpose eq18094 eq37
    | (have j1 := eq18094 X0
       grind)
    | exact resolve eq37 eq18094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18094
  have eq18689 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq18332 (σ X0)
       grind)
    | exact superpose eq18332 eq15
    | (have j1 := eq18332 (σ X0)
       grind)
    | exact resolve eq15 eq18332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18332
  have eq32691 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17996 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq17996
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq17996 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17996
  have eq32798 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32691 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32691
  have eq34798 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) = (M.op (M.op X4 X3) (M.op X3 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq162 X3 X1 X4
       have i₂ := eq373 X0 X1 X2 X3
       grind)
    | exact superpose eq373 eq162
    | exact resolve eq162 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq373
  have eq39014 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq343 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq32798 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq32798 eq343
    | (have j1 := eq32798 X0 x
       grind)
    | exact resolve eq343 eq32798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32798
  have eq47565 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X3 X2) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34798 X0 X1 (M.op X0 X1) X2 X3
       have i₂ := eq611 X1 X0
       grind)
    | exact superpose eq611 eq34798
    | exact resolve eq34798 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq34798
  have eq59417 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq37 x x
       have i₂ := eq3652
       grind)
    | exact superpose eq3652 eq37
    | exact resolve eq37 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq59527 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq59417
  have eq161129 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (σ X0)
       have i₂ := eq18689 X0
       grind)
    | exact superpose eq18689 eq45
    | (have j1 := eq18689 X0
       grind)
    | exact resolve eq45 eq18689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161325 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq18689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18689
  have eq161400 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq161129 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq161129
    | (have j0 := eq161129 X0
       grind)
    | exact resolve eq161129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161129
  have eq161430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq161400 X0
       have j1 := eq161325 X0
       grind)
    | (have r₁ := eq161400 X0
       have r₂ := eq161325 X0
       grind)
    | exact resolve eq161400 eq161325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161325 eq161400
  have eq162274 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq161430 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq161430
    | exact resolve eq161430 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162381 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq161430 X0
       grind)
    | exact superpose eq161430 eq92
    | exact resolve eq92 eq161430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq162430 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45 (σ X0)
       have i₂ := eq161430 X0
       grind)
    | exact superpose eq161430 eq45
    | exact resolve eq45 eq161430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq162786 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq162430 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq162430
    | exact resolve eq162430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162430
  have eq162807 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq162381 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq162381
    | exact resolve eq162381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162381
  have eq162854 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq162274 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq162274
    | exact resolve eq162274 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq162274
  have eq162931 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq162854 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq162854
    | exact resolve eq162854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162854
  have eq164808 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq161430 (k X0 (k X0 X0))
       have i₂ := eq162786 X0
       grind)
    | exact superpose eq162786 eq161430
    | exact resolve eq161430 eq162786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162786
  have eq164816 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq164808 X0
       have i₂ := eq162931 (k X0 (k X0 X0))
       grind)
    | exact superpose eq162931 eq164808
    | exact resolve eq164808 eq162931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164808
  have eq164943 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq164816 X0
       have i₂ := eq162807 X0
       grind)
    | exact superpose eq162807 eq164816
    | exact resolve eq164816 eq162807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162807 eq164816
  have eq171008 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq164943 X0
       grind)
    | exact superpose eq164943 eq37
    | exact resolve eq37 eq164943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq171110 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq343 (σ X0) (σ X0)
       have i₂ := eq164943 X0
       grind)
    | exact superpose eq164943 eq343
    | exact resolve eq343 eq164943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171173 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2302 X0 (σ X0) (σ X0)
       have i₂ := eq164943 X0
       grind)
    | exact superpose eq164943 eq2302
    | exact resolve eq2302 eq164943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq181559 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X2)) = (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq171008 (M.op X1 X2) X3
       have i₂ := eq47565 X1 X2 X1 X0
       grind)
    | (have i₁ := eq171008 (M.op X1 X1) X1
       have i₂ := eq47565 X0 X1 X1 X1
       grind)
    | exact superpose eq47565 eq171008
    | exact resolve eq171008 eq47565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171008
  have eq303319 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq171173 (M.op X2 X1) X1
       have i₂ := eq47565 X2 X1 X2 X3
       grind)
    | (have i₁ := eq171173 (M.op X1 X1) X1
       have i₂ := eq47565 X0 X1 X1 X1
       grind)
    | exact superpose eq47565 eq171173
    | exact resolve eq171173 eq47565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47565 eq171173
  have eq303957 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq303319 X0 X1 X2 x
       have i₂ := eq181559 X0 X1 X2 x
       grind)
    | exact superpose eq181559 eq303319
    | exact resolve eq303319 eq181559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181559 eq303319
  have eq304277 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (k (M.op X1 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq303957 X0 X1 X2
       have i₂ := eq161430 (M.op X1 X2)
       grind)
    | exact superpose eq161430 eq303957
    | exact resolve eq303957 eq161430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303957
  have eq304456 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X2) (M.op X1 X2))) = (σ (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq304277 X0 X1 X2
       have i₂ := eq162931 (M.op X1 X2)
       grind)
    | exact superpose eq162931 eq304277
    | exact resolve eq304277 eq162931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304277
  have eq304575 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq304456 X0 X1 X2
       have i₂ := eq371 X2 X1
       grind)
    | exact superpose eq371 eq304456
    | exact resolve eq304456 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq304456
  have eq2218802 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq39014 y
       have i₂ := eq59527
       grind)
    | exact superpose eq59527 eq39014
    | exact resolve eq39014 eq59527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39014 eq59527
  have eq2219360 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2218802
  have eq2219902 : (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2219360
       have i₂ := eq161430 x
       grind)
    | exact superpose eq161430 eq2219360
    | exact resolve eq2219360 eq161430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219360
  have eq2220558 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2219902
       have i₂ := eq162931 x
       grind)
    | exact superpose eq162931 eq2219902
    | exact resolve eq2219902 eq162931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219902
  have eq2221208 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq2220558
       have i₂ := eq161430 y
       grind)
    | exact superpose eq161430 eq2220558
    | exact resolve eq2220558 eq161430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220558
  have eq2221855 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2221208
       have i₂ := eq162931 y
       grind)
    | exact superpose eq162931 eq2221208
    | exact resolve eq2221208 eq162931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221208
  have eq2222159 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2221855
       grind)
    | exact superpose eq2221855 eq16
    | exact resolve eq16 eq2221855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221855
  have eq2222162 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2222159
       have r₂ := eq164943 x
       grind)
    | exact resolve eq2222159 eq164943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222159
  have eq2222706 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq164943 (M.op x x)
       have i₂ := eq2222162
       grind)
    | exact superpose eq2222162 eq164943
    | exact resolve eq164943 eq2222162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164943 eq2222162
  have eq2222808 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2222706
       have i₂ := eq304575 x x x
       grind)
    | exact superpose eq304575 eq2222706
    | exact resolve eq2222706 eq304575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304575 eq2222706
  have eq2223308 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2222808
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq2222808
    | exact resolve eq2222808 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2222808
  have eq2223728 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2223308
       have i₂ := eq161430 y
       grind)
    | exact superpose eq161430 eq2223308
    | exact resolve eq2223308 eq161430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161430 eq2223308
  have eq2223959 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2223728
       have i₂ := eq162931 y
       grind)
    | exact superpose eq162931 eq2223728
    | exact resolve eq2223728 eq162931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162931 eq2223728
  have eq2223960 : (σ x) = (σ (M.op y y)) := by grind
  clear eq2223959
  have eq2227579 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq171110 y
       have i₂ := eq2223960
       grind)
    | exact superpose eq2223960 eq171110
    | exact resolve eq171110 eq2223960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171110
  have eq2227620 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2223960
       grind)
    | exact superpose eq2223960 eq10
    | exact resolve eq10 eq2223960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223960
  have eq2228587 : x = (M.op y y) := by
    first
    | (have i₁ := eq2227620
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2227620
    | exact resolve eq2227620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227620
  have eq2230463 : x = (M.op x y) := by
    first
    | (have i₁ := eq343 y y
       have i₂ := eq2228587
       grind)
    | exact superpose eq2228587 eq343
    | exact resolve eq343 eq2228587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq2228587
  have eq2262140 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2227579
       grind)
    | exact superpose eq2227579 eq16
    | exact resolve eq16 eq2227579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227579
  have eq2262954 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2262140
       have i₂ := eq2230463
       grind)
    | exact superpose eq2230463 eq2262140
    | exact resolve eq2262140 eq2230463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230463 eq2262140
  have eq2262955 : False := by grind
  exact eq2262955

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_x_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq65 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq65
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq57
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq74
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq103
    | exact resolve eq103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq246 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq28 eq53
    | (have j0 := eq53 (σ y) (σ x)
       grind)
    | exact resolve eq53 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq643 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq51
    | (have j1 := eq62 X0 X0
       grind)
    | exact resolve eq51 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq658 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq3369 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq418
    | exact resolve eq418 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq3396 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq28 eq3369
    | (have j0 := eq3369 (σ y) (σ x)
       grind)
    | exact resolve eq3369 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3700 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq658 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq658
    | (have j0 := eq658 (τ X0)
       grind)
    | exact resolve eq658 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3717 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3700 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3700
    | (have j0 := eq3700 X0
       grind)
    | exact resolve eq3700 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3700
  have eq3729 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3717 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3717
    | (have j0 := eq3717 X0
       grind)
    | exact resolve eq3717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717
  have eq3969 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq422 X0 X0 X2 X3 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq422
    | exact resolve eq422 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq17247 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3969 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq51 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq3969
    | exact resolve eq3969 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3969
  have eq22504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq22505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq22504
    | exact resolve eq22504 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22504
  have eq22516 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22505
       have r₂ := eq29
       grind)
    | exact resolve eq22505 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22505
  have eq22541 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22516 eq53
    | exact resolve eq53 eq22516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22516
  have eq22554 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq22541
  have eq22607 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22554 eq17247
    | exact resolve eq17247 eq22554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22554
  have eq22610 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq22607
    | exact resolve eq22607 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22607
  have eq22644 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq22610
       grind)
    | exact superpose eq22610 eq53
    | exact resolve eq53 eq22610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22610
  have eq22657 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22644
  have eq22687 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq22699 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq22657
       grind)
    | exact superpose eq22657 eq53
    | exact resolve eq53 eq22657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq22710 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17247 y y
       have i₂ := eq22657
       grind)
    | exact superpose eq22657 eq17247
    | exact resolve eq17247 eq22657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17247 eq22657
  have eq22713 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22710
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq22710
    | exact resolve eq22710 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22710
  have eq22727 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22713 eq246
    | exact resolve eq246 eq22713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq22733 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22713 eq3396
    | exact resolve eq3396 eq22713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396
  have eq22780 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq22733
    | exact resolve eq22733 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22733
  have eq23992 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq22699
       grind)
    | exact superpose eq22699 eq68
    | exact resolve eq68 eq22699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq22699
  have eq24033 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23992
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq23992
    | exact resolve eq23992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23992
  have eq26331 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22780 eq22727
    | exact resolve eq22727 eq22780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22727 eq22780
  have eq26365 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq26331
  have eq26369 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22713 eq26365
    | exact resolve eq26365 eq22713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22713 eq26365
  have eq26397 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq26369
  have eq26398 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26397 eq76
    | exact resolve eq76 eq26397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq26397
  have eq26442 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq26398
    | exact resolve eq26398 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26398
  have eq28926 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24033 eq57
    | exact resolve eq57 eq24033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28946 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24033 eq3729
    | (have j0 := eq3729 (σ x)
       grind)
    | exact resolve eq3729 eq24033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24033
  have eq28958 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq28946
    | exact resolve eq28946 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28946
  have eq28959 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq28958
  have eq28968 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq28926
    | exact resolve eq28926 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28926
  have eq29103 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq28959
  have eq29634 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29103 eq57
    | exact resolve eq57 eq29103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29103
  have eq29687 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30 eq29634
    | exact resolve eq29634 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29634
  have eq29780 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3729 x
       have i₂ := eq26442
       grind)
    | exact superpose eq26442 eq3729
    | (have j0 := eq3729 x
       grind)
    | exact resolve eq3729 eq26442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq29797 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29780
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq29780
    | exact resolve eq29780 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29780
  have eq29798 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq29797
  have eq29845 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28968
       have i₂ := eq29687
       grind)
    | exact superpose eq29687 eq28968
    | exact resolve eq28968 eq29687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28968 eq29687
  have eq29870 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq29845
  have eq29899 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq29870 eq29
    | exact resolve eq29 eq29870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29870
  have eq34136 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq29798
  have eq35093 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26442
       have i₂ := eq34136
       grind)
    | exact superpose eq34136 eq26442
    | exact resolve eq26442 eq34136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26442 eq34136
  have eq35120 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq35093
  have eq35412 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq35120 eq31
    | exact resolve eq31 eq35120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq35120
  have eq35672 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq35412
    | exact resolve eq35412 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35412
  have eq35673 : x = (M.op x y) ∨ x = y := by grind
  clear eq35672
  have eq35674 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq35673 eq22
    | exact resolve eq22 eq35673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35673
  have eq35871 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq35674
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35674
    | exact resolve eq35674 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35674
  have eq35872 : x = y := by
    first
    | (have r₁ := eq35871
       have r₂ := eq29899
       grind)
    | exact resolve eq35871 eq29899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29899 eq35871
  have eq35873 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq35872
       grind)
    | exact superpose eq35872 eq20
    | exact resolve eq20 eq35872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq35874 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq35872
       grind)
    | exact superpose eq35872 eq26
    | exact resolve eq26 eq35872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35996 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22687
       have i₂ := eq35872
       grind)
    | exact superpose eq35872 eq22687
    | exact resolve eq22687 eq35872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22687 eq35872
  have eq36084 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq35874
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35874
    | exact resolve eq35874 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35874
  have eq36089 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq36084 eq28
    | exact resolve eq28 eq36084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq36084
  have eq36452 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq41377 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq658 x
       have i₂ := eq35996
       grind)
    | exact superpose eq35996 eq658
    | (have j0 := eq658 x
       grind)
    | exact resolve eq658 eq35996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq35996
  have eq41398 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41377
  have eq41414 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41398
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41398
    | exact resolve eq41398 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41398
  have eq41434 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36089 eq41414
    | exact resolve eq41414 eq36089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36089 eq41414
  have eq41435 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41434
  have eq41454 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq41435 eq29
    | exact resolve eq29 eq41435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41532 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq41435 eq36452
    | exact resolve eq36452 eq41435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36452 eq41435
  have eq41634 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq41532 eq57
    | exact resolve eq57 eq41532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq41532
  have eq41698 : x = (k x x) := by
    first
    | exact superpose eq30 eq41634
    | exact resolve eq41634 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq41634
  have eq41742 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq41698
       grind)
    | exact superpose eq41698 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq41698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41698
  have eq41743 : x = (M.op x x) := by grind
  clear eq41742
  have eq41757 : x = (M.op x y) := by
    first
    | (have i₁ := eq41743
       have i₂ := eq35873
       grind)
    | exact superpose eq35873 eq41743
    | exact resolve eq41743 eq35873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35873 eq41743
  have eq41796 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq41757 eq22
    | exact resolve eq22 eq41757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq41757
  have eq42051 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41796
    | exact resolve eq41796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq41796
  have eq42124 : False := by grind
  exact eq42124

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq85 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq16
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq114 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq117
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq163 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq201 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq163
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq163
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq203 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq201
  have eq260 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq402 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq67
    | exact resolve eq67 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq413 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq402 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq402
    | (have j0 := eq402 y x
       grind)
    | exact resolve eq402 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq98 X0 X0
       grind)
    | exact superpose eq98 eq54
    | (have j1 := eq98 X0 X0
       grind)
    | exact resolve eq54 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq864 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq4131 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq864 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq864
    | (have j0 := eq864 (τ X0)
       grind)
    | exact resolve eq864 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq864
  have eq4157 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4131 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4131
    | (have j0 := eq4131 X0
       grind)
    | exact resolve eq4131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4131
  have eq4168 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4157 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4157
    | (have j0 := eq4157 X0
       grind)
    | exact resolve eq4157 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157
  have eq26630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq26630
    | exact resolve eq26630 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26630
  have eq26644 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26631
       have r₂ := eq28
       grind)
    | exact resolve eq26631 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26631
  have eq26660 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26644 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26644
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26644
       grind)
    | exact resolve eq12 eq26644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26644
  have eq26682 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26660
  have eq26683 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26682
  have eq26713 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26683 eq260
    | exact resolve eq260 eq26683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26683
  have eq26745 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26713
  have eq26770 : (τ (σ x)) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26745 eq92
    | exact resolve eq92 eq26745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq26771 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26745 eq118
    | exact resolve eq118 eq26745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq26745
  have eq26785 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq26771
  have eq26794 : x = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq26770
    | exact resolve eq26770 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26770
  have eq26797 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq26794
       have r₂ := eq12 y x
       grind)
    | exact resolve eq26794 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26794
  have eq26810 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq260 x
       have i₂ := eq26797
       grind)
    | exact superpose eq26797 eq260
    | exact resolve eq260 eq26797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26797
  have eq26842 : x = (k y x) := by grind
  clear eq26810
  have eq28278 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq402 x y
       have i₂ := eq26785
       grind)
    | exact superpose eq26785 eq402
    | exact resolve eq402 eq26785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq34943 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26785
       have i₂ := eq28278
       grind)
    | exact superpose eq28278 eq26785
    | exact resolve eq26785 eq28278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26785 eq28278
  have eq34997 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq34943
  have eq35019 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq34997
       grind)
    | exact superpose eq34997 eq54
    | exact resolve eq54 eq34997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq34997
  have eq35083 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35019
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35019
    | exact resolve eq35019 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35019
  have eq35193 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35083 eq29
    | exact resolve eq29 eq35083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35083
  have eq35349 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq35193
    | exact resolve eq35193 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35193
  have eq35350 : x = (M.op x y) := by grind
  clear eq35349
  have eq35361 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq35350 eq21
    | exact resolve eq21 eq35350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq35414 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq35350 eq413
    | exact resolve eq413 eq35350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq35503 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq35414
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35414
    | exact resolve eq35414 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq35414
  have eq35551 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35361
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35361
    | exact resolve eq35361 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35361
  have eq35555 : x = (M.op y y) := by
    first
    | exact superpose eq35350 eq35503
    | exact resolve eq35503 eq35350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35503
  have eq35568 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq35551 eq27
    | exact resolve eq27 eq35551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35773 : y = (M.op x x) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq35555
       grind)
    | exact superpose eq35555 eq56
    | exact resolve eq56 eq35555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq35555
  have eq36121 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq35773
       grind)
    | exact superpose eq35773 eq114
    | exact resolve eq114 eq35773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq35773
  have eq36208 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq35551 eq36121
    | exact resolve eq36121 eq35551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36121
  have eq36218 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq36208
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36208
    | exact resolve eq36208 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36208
  have eq41903 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq36218 eq4168
    | (have j0 := eq4168 (σ (M.op x y))
       grind)
    | exact resolve eq4168 eq36218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq41920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq35568 eq41903
    | exact resolve eq41903 eq35568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41903
  have eq41932 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq41920
       have r₂ := eq28
       grind)
    | exact resolve eq41920 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41920
  have eq42053 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq41932 eq260
    | exact resolve eq260 eq41932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq41932
  have eq43420 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq42053 eq36218
    | exact resolve eq36218 eq42053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36218 eq42053
  have eq43441 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq43420
  have eq43479 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq43441 eq30
    | exact resolve eq30 eq43441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq43441
  have eq43702 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq43479
    | exact resolve eq43479 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq43479
  have eq43768 : x = y ∨ x = y := by
    first
    | exact superpose eq35350 eq43702
    | exact resolve eq43702 eq35350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43702
  have eq43769 : x = y := by grind
  clear eq43768
  have eq43823 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq43769
       grind)
    | exact superpose eq43769 eq25
    | exact resolve eq25 eq43769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq43937 : x = (k x x) := by
    first
    | (have i₁ := eq26842
       have i₂ := eq43769
       grind)
    | exact superpose eq43769 eq26842
    | exact resolve eq26842 eq43769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26842 eq43769
  have eq44059 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43823
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43823
    | exact resolve eq43823 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43823
  have eq44141 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq35551 eq44059
    | exact resolve eq44059 eq35551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44059
  have eq44363 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44141 eq35568
    | exact resolve eq35568 eq44141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35568 eq44141
  have eq45433 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44363 eq203
    | exact resolve eq203 eq44363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq44363
  have eq45527 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq45433
       have r₂ := eq28
       grind)
    | exact resolve eq45433 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45433
  have eq45538 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq35350 eq45527
    | exact resolve eq45527 eq35350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35350 eq45527
  have eq45542 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45538
       have i₂ := eq43937
       grind)
    | exact superpose eq43937 eq45538
    | exact resolve eq45538 eq43937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43937 eq45538
  have eq45543 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45542 eq15
    | exact resolve eq15 eq45542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45542
  have eq45637 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45543
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45543
    | exact resolve eq45543 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45543
  have eq45671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35551 eq45637
    | exact resolve eq45637 eq35551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35551 eq45637
  have eq45693 : False := by grind
  exact eq45693
