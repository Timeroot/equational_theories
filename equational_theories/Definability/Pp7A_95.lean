import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation626`: `x = x ◇ (x ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation626 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law626 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law626.models_iff G M).mp hM
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
  have eq69 : y ≠ (M.op x y) ∨ x = y ∨ y = (k y x) := by
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
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
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
  clear eq37
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq873
    | exact resolve eq873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq877 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq874
       have r₂ := eq28
       grind)
    | exact resolve eq874 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq879 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq877
    | exact resolve eq877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq947 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq879 eq28
    | exact resolve eq28 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq879 eq70
    | (have r₁ := eq70
       have r₂ := eq879
       grind)
    | exact resolve eq70 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq879
  have eq953 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq949
  have eq954 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq953
  have eq1015 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq954 eq102
    | exact resolve eq102 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq954
  have eq1019 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1015
  have eq1024 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1019
       have r₂ := eq947
       grind)
    | exact resolve eq1019 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947 eq1019
  have eq1029 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1024 eq30
    | exact resolve eq30 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1047 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1029
    | exact resolve eq1029 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1048 : y = (M.op x y) ∨ x = y := by grind
  clear eq1047
  have eq1051 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1048 eq21
    | exact resolve eq21 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq1048 eq69
    | (have r₁ := eq69
       have r₂ := eq1048
       grind)
    | exact resolve eq69 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1048
  have eq1065 : y ≠ y ∨ x = y ∨ y = (k y x) := by grind
  clear eq1054
  have eq1066 : y = (k y x) ∨ x = y := by grind
  clear eq1065
  have eq1075 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1051
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1051
    | exact resolve eq1051 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1157 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq1066
       grind)
    | exact superpose eq1066 eq87
    | exact resolve eq87 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1066
  have eq1162 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1157
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1157
    | exact resolve eq1157 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1222 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1162 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1223 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1222
  have eq1229 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1223
    | exact resolve eq1223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1296 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1229 eq28
    | exact resolve eq28 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1304 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1296
       have r₂ := eq1075
       grind)
    | exact resolve eq1296 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq1296
  have eq1307 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1304 eq30
    | exact resolve eq30 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1304
  have eq1330 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1307
    | exact resolve eq1307 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1307
  have eq1331 : x = y := by grind
  clear eq1330
  have eq1386 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq19
    | exact resolve eq19 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1387 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq25
    | exact resolve eq25 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1331
  have eq1406 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1387
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1387
    | exact resolve eq1387 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1387
  have eq1410 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1406 eq27
    | exact resolve eq27 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1406
  have eq1449 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1410 eq68
    | exact resolve eq68 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1410
  have eq1458 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1449
       have i₂ := eq1386
       grind)
    | exact superpose eq1386 eq1449
    | exact resolve eq1449 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386 eq1449
  have eq1461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1458 eq15
    | exact resolve eq15 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1461
    | exact resolve eq1461 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1461
  have eq1498 : False := by grind
  exact eq1498

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_x_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq419 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq680 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq419 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq419
    | exact resolve eq419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq702 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq680
  have eq704 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq702 X0 X1
       have j1 := eq91 X1 X0
       grind)
    | (have r₁ := eq702 X1 X0
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq702 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq702 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq702
  have eq706 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq704
    | exact resolve eq704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq704 (σ X0) X1
       grind)
    | exact superpose eq704 eq15
    | (have j1 := eq704 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq750 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq706 (τ X1) X0
       grind)
    | exact superpose eq706 eq19
    | (have j1 := eq706 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq706
  have eq833 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq750 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq750
    | exact resolve eq750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq875 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq833 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq833
    | (have j0 := eq833 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq1061 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq719 x y
       grind)
    | exact superpose eq719 eq16
    | (have j1 := eq719 x y
       grind)
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq1077 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1061
       have i₂ := eq875 y x
       grind)
    | exact superpose eq875 eq1061
    | (have j1 := eq875 (σ x) (σ y)
       grind)
    | (have r₁ := eq1061
       have r₂ := eq875 y x
       grind)
    | (have r₁ := eq1061
       have r₂ := eq875 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1061
       have r₂ := eq875 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1061 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq1061
  have eq1078 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1077
  have eq1081 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1078
       grind)
    | exact superpose eq1078 eq16
    | exact resolve eq16 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1082 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1081
       have r₂ := eq77 x
       grind)
    | exact resolve eq1081 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1083 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq16
    | exact resolve eq16 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq10
    | exact resolve eq10 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1130 : x = y := by
    first
    | (have i₁ := eq1084
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1084
    | exact resolve eq1084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1131 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1083
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq1083
    | exact resolve eq1083 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1083
  have eq1132 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1131
       have i₂ := eq1130
       grind)
    | exact superpose eq1130 eq1131
    | exact resolve eq1131 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq1131
  have eq1133 : False := by grind
  exact eq1133

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X1) (M.op X0 (σ X1))
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq84
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | (have j0 := eq90 X0
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq91 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq91 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq92 (σ X0)
       grind)
    | exact superpose eq92 eq15
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq95
    | exact resolve eq95 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq95
  have eq229 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq4320 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq12
    | (have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq82 (M.op X0 (σ X1)) X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq4335 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320
  have eq8251 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4335 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4335
    | exact resolve eq4335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8284 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq4335 X0 X1
       grind)
    | exact superpose eq4335 eq24
    | (have j1 := eq4335 X0 X1
       grind)
    | exact resolve eq24 eq4335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4335
  have eq8384 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8284 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8284
    | (have j0 := eq8284 X0 X1
       grind)
    | exact resolve eq8284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8284
  have eq8391 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8251 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq8251
    | (have j0 := eq8251 X0 X1
       grind)
    | exact resolve eq8251 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8251
  have eq8530 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq8391 X1 X0
       grind)
    | exact superpose eq8391 eq11
    | (have j1 := eq8391 X1 X0
       grind)
    | exact resolve eq11 eq8391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8391
  have eq8660 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8530 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq8530
    | (have j0 := eq8530 X0 X1
       grind)
    | exact resolve eq8530 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8530
  have eq8750 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq8660 (τ X0) X1
       grind)
    | exact superpose eq8660 eq18
    | (have j1 := eq8660 (τ X0) X1
       grind)
    | exact resolve eq18 eq8660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8660
  have eq8966 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X1)) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8384 (τ X0) X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq8384
    | (have j0 := eq8384 (τ X1) X0
       grind)
    | exact resolve eq8384 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq8384
  have eq9115 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8966 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8966
    | (have j0 := eq8966 X0 X1
       grind)
    | exact resolve eq8966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8966
  have eq9156 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9115 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9115
    | (have j0 := eq9115 X0 X1
       grind)
    | exact resolve eq9115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9115
  have eq9466 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq9156 X0 X1
       grind)
    | exact superpose eq9156 eq11
    | (have j1 := eq9156 X0 X1
       grind)
    | exact resolve eq11 eq9156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9156
  have eq9600 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9466 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq9466
    | (have j0 := eq9466 X0 X1
       grind)
    | exact resolve eq9466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9466
  have eq9893 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9600 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9600
    | (have j0 := eq9600 (τ (σ (k X0 X1))) (τ (σ X1))
       grind)
    | exact resolve eq9600 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9600
  have eq10084 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9893 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9893
    | (have j0 := eq9893 X0 X1
       grind)
    | exact resolve eq9893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893
  have eq10093 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10084 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq10084
    | (have j0 := eq10084 X0 X1
       grind)
    | exact resolve eq10084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10084
  have eq10925 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8750 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8750
    | exact resolve eq8750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8750
  have eq11046 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10925 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10925
    | (have j0 := eq10925 X0 X1
       grind)
    | exact resolve eq10925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10925
  have eq11597 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10093 x y
       grind)
    | exact superpose eq10093 eq16
    | (have j1 := eq10093 x y
       grind)
    | exact resolve eq16 eq10093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10093
  have eq11827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11597
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq11597
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq11597
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq11597
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11597 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11828 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq11597
       have i₂ := eq11046 x y
       grind)
    | exact superpose eq11046 eq11597
    | (have j1 := eq11046 x y
       grind)
    | (have r₁ := eq11597
       have r₂ := eq11046 x y
       grind)
    | (have r₁ := eq11597
       have r₂ := eq11046 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq11597
       have r₂ := eq11046 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11597 eq11046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046 eq11597
  have eq11831 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq11828
  have eq11832 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq11831
  have eq11833 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11827
  have eq11834 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11833
  have eq11837 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11832
       grind)
    | exact superpose eq11832 eq16
    | exact resolve eq16 eq11832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11832
  have eq11838 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11837
       have r₂ := eq106 x
       grind)
    | exact resolve eq11837 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11837
  have eq12020 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq229 x y
       have i₂ := eq11838
       grind)
    | exact superpose eq11838 eq229
    | (have j0 := eq229 x y
       grind)
    | exact resolve eq229 eq11838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq11838
  have eq12035 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12020
  have eq12036 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq12035
  have eq12228 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq16
    | exact resolve eq16 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036
  have eq12249 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12228
       have i₂ := eq11834
       grind)
    | exact superpose eq11834 eq12228
    | exact resolve eq12228 eq11834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11834 eq12228
  have eq12253 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12249
  have eq12254 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq12253
  have eq12336 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12254
       grind)
    | exact superpose eq12254 eq16
    | exact resolve eq16 eq12254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12254
  have eq12337 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq12336
       have r₂ := eq106 x
       grind)
    | exact resolve eq12336 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12336
  have eq12338 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12337
       grind)
    | exact superpose eq12337 eq16
    | exact resolve eq16 eq12337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12339 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12337
       grind)
    | exact superpose eq12337 eq10
    | exact resolve eq10 eq12337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12337
  have eq12418 : x = y := by
    first
    | (have i₁ := eq12339
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12339
    | exact resolve eq12339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12339
  have eq12419 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12338
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq12338
    | exact resolve eq12338 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq12338
  have eq12424 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12419
       have i₂ := eq12418
       grind)
    | exact superpose eq12418 eq12419
    | exact resolve eq12419 eq12418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12418 eq12419
  have eq12425 : False := by grind
  exact eq12425

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq50 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq50 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq169 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq176 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq169 X1 X0
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq169 X0 X0
       have r₂ := eq54 X0 X0
       grind)
    | exact resolve eq169 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq169
  have eq375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq176 (σ X0) (σ X1)
       grind)
    | exact superpose eq176 eq15
    | exact resolve eq15 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 X1
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq375
    | exact resolve eq375 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq375
  have eq385 : False := by grind
  exact eq385

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq82
  have eq215 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq243 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq215
  have eq249 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq243 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq243 (σ X0) (M.op X0 X0)
       have r₂ := eq76 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq243 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq243
  have eq416 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq249 (σ X0) X1
       grind)
    | exact superpose eq249 eq15
    | (have j1 := eq249 (σ X0) X1
       grind)
    | exact resolve eq15 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1471 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq416 x y
       grind)
    | exact superpose eq416 eq16
    | (have j1 := eq416 x y
       grind)
    | exact resolve eq16 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1491 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq416 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq1535 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1491 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq1491
    | (have j0 := eq1491 (τ X0) (τ X1)
       grind)
    | exact resolve eq1491 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1544 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1535 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1535
    | (have j0 := eq1535 X0 X1
       grind)
    | exact resolve eq1535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1547 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1544 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1544
    | (have j0 := eq1544 X0 X1
       grind)
    | exact resolve eq1544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1548 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1547 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1547
    | (have j0 := eq1547 X0 X1
       grind)
    | exact resolve eq1547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1549 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1548 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1548
    | (have j0 := eq1548 X0 X1
       grind)
    | exact resolve eq1548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq10394 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq83 X1 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq10413 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq10394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10394
  have eq10414 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10413
  have eq130726 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq10414 X1 X0
       grind)
    | exact superpose eq10414 eq11
    | (have j1 := eq10414 X1 X0
       grind)
    | exact resolve eq11 eq10414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10414
  have eq130972 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq130726 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq130726
    | (have j0 := eq130726 X0 X1
       grind)
    | exact resolve eq130726 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq130726
  have eq131100 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq130972 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq130972 X0 (σ X0)
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq130972 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq130972 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130972
  have eq132487 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq131100 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq131100
    | exact resolve eq131100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131100
  have eq133837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1471
       have i₂ := eq132487 x y
       grind)
    | exact superpose eq132487 eq1471
    | (have j1 := eq132487 x y
       grind)
    | exact resolve eq1471 eq132487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq133839 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq132487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132487
  have eq133841 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq133837
  have eq135236 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq133839 (σ x) (σ y)
       have i₂ := eq133841
       grind)
    | exact superpose eq133841 eq133839
    | (have j0 := eq133839 (σ x) (σ y)
       grind)
    | (have r₁ := eq133839 (σ x) (σ y)
       have r₂ := eq133841
       grind)
    | exact resolve eq133839 eq133841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133841
  have eq135237 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq135236
  have eq135244 : y = (k x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq135237
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq135237
    | exact resolve eq135237 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135237
  have eq135954 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1491 x y
       have i₂ := eq135244
       grind)
    | exact superpose eq135244 eq1491
    | (have j0 := eq1491 x y
       grind)
    | (have r₁ := eq1491 x y
       have r₂ := eq135244
       grind)
    | exact resolve eq1491 eq135244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135244
  have eq136068 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq135954
  have eq136092 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1491 x y
       grind)
    | (have r₁ := eq136068
       have r₂ := eq1491 x y
       grind)
    | exact resolve eq136068 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491 eq136068
  have eq136652 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq136092
       grind)
    | exact superpose eq136092 eq16
    | exact resolve eq16 eq136092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136662 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq133839 (σ x) (σ y)
       have i₂ := eq136092
       grind)
    | exact superpose eq136092 eq133839
    | (have j0 := eq133839 (σ x) (σ y)
       grind)
    | (have r₁ := eq133839 (σ x) (σ y)
       have r₂ := eq136092
       grind)
    | exact resolve eq133839 eq136092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133839 eq136092
  have eq136663 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq136662
  have eq136670 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq136663
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq136663
    | exact resolve eq136663 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136663
  have eq137954 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq136670
       grind)
    | exact superpose eq136670 eq10
    | exact resolve eq10 eq136670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136670
  have eq138297 : y = (k x y) := by
    first
    | (have i₁ := eq137954
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq137954
    | exact resolve eq137954 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137954
  have eq138810 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1549 x y
       have i₂ := eq138297
       grind)
    | exact superpose eq138297 eq1549
    | (have j0 := eq1549 x y
       grind)
    | (have r₁ := eq1549 x y
       have r₂ := eq138297
       grind)
    | exact resolve eq1549 eq138297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq138297
  have eq138920 : y = (M.op x y) := by grind
  clear eq138810
  have eq140090 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq136652
       have i₂ := eq138920
       grind)
    | exact superpose eq138920 eq136652
    | exact resolve eq136652 eq138920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136652 eq138920
  have eq140102 : False := by grind
  exact eq140102

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq85 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq184 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq166 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq166
    | (have j0 := eq166 X0 X1
       grind)
    | exact resolve eq166 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq189 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq85 X1 X0
       grind)
    | (have r₁ := eq184 X1 X0
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq184 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq184 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq184
  have eq193 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq189 (σ X0) X1
       grind)
    | exact superpose eq189 eq15
    | (have j1 := eq189 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq193 X1 (τ X0)
       grind)
    | exact superpose eq193 eq18
    | (have j1 := eq193 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq193
  have eq420 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq207 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq207
    | exact resolve eq207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq457 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq420 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq420
    | (have j0 := eq420 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq967 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198 x y
       grind)
    | exact superpose eq198 eq16
    | (have j1 := eq198 x y
       grind)
    | exact resolve eq16 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq967
       have i₂ := eq457 x y
       grind)
    | exact superpose eq457 eq967
    | (have j1 := eq457 (σ x) (σ y)
       grind)
    | (have r₁ := eq967
       have r₂ := eq457 x y
       grind)
    | (have r₁ := eq967
       have r₂ := eq457 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq967
       have r₂ := eq457 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq967 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq967
  have eq991 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq990
  have eq995 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq991
       grind)
    | exact superpose eq991 eq10
    | exact resolve eq10 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1038 : x = y ∨ x = y := by
    first
    | (have i₁ := eq995
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq995
    | exact resolve eq995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1039 : x = y := by grind
  clear eq1038
  have eq1127 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq16
    | exact resolve eq16 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1128 : False := by grind
  exact eq1128

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq270 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq275 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq381 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq275 X1 X0
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 (σ x) (σ y)
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq389 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq384
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq384
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq390 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq388 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq416 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq390 X1 (τ X0)
       grind)
    | exact superpose eq390 eq17
    | (have j1 := eq390 X1 (τ X0)
       grind)
    | exact resolve eq17 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq422 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq390 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq416 X1 (τ X0)
       grind)
    | exact superpose eq416 eq18
    | (have j1 := eq416 X1 (τ X0)
       grind)
    | exact resolve eq18 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq416
  have eq637 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq632
    | (have j0 := eq632 X0 X1
       grind)
    | exact resolve eq632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq653 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq656 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq653
    | (have j0 := eq653 X0 X1
       grind)
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq751 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq656 X0 X1
       have i₂ := eq390 X0 X1
       grind)
    | exact superpose eq390 eq656
    | (have j0 := eq656 X1 X0
       have j1 := eq390 X1 X0
       grind)
    | exact resolve eq656 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq656
  have eq810 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq751 X0 X1
       have j1 := eq422 X0 X1
       grind)
    | (have r₁ := eq751 X0 X1
       have r₂ := eq422 X0 X1
       grind)
    | exact resolve eq751 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq751
  have eq851 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq810 X1 (σ X0)
       grind)
    | exact superpose eq810 eq22
    | (have j1 := eq810 X1 (σ X0)
       grind)
    | exact resolve eq22 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq810
  have eq884 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq904 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq884
    | (have j0 := eq884 X0 X1
       grind)
    | exact resolve eq884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq1132 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq904 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq904
    | exact resolve eq904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1200 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1132 x y
       grind)
    | exact superpose eq1132 eq16
    | (have j1 := eq1132 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1132 x y
       grind)
    | exact resolve eq16 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1213 : y = (k x y) := by grind
  clear eq1200
  have eq1811 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq389
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq389
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq389 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1814 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1811
  have eq1815 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1814
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq1814
    | exact resolve eq1814 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1816 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1815
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq1815
    | exact resolve eq1815 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1817 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq1816
       grind)
    | exact superpose eq1816 eq389
    | exact resolve eq389 eq1816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1816
  have eq1828 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1817
  have eq1829 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1828
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq1828
    | exact resolve eq1828 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1830 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1829
  have eq1833 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1830
       grind)
    | exact superpose eq1830 eq16
    | exact resolve eq16 eq1830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq1865 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1833
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq1833
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq1833 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1868 : (M.op x y) = (k x y) := by grind
  clear eq1865
  have eq1870 : y = (M.op x y) := by
    first
    | (have i₁ := eq1868
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq1868
    | exact resolve eq1868 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq1868
  have eq1871 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1833
       have i₂ := eq1870
       grind)
    | exact superpose eq1870 eq1833
    | exact resolve eq1833 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833 eq1870
  have eq1884 : False := by grind
  exact eq1884

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
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
  have eq381 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
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
  have eq387 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq390 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq392 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq390 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq390 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq390 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq390 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq395 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq387
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq387 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq401 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq391 (M.op X1 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq391 X0 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq391 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq391 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq410 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq395
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq395
    | exact resolve eq395 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq411 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq401 X0 X1
       have j1 := eq392 X0 X1
       grind)
    | (have r₁ := eq401 X0 X1
       have r₂ := eq392 X0 X1
       grind)
    | (have r₁ := eq401 X1 X0
       have r₂ := eq392 X0 X1
       grind)
    | (have r₁ := eq401 X1 X1
       have r₂ := eq392 (k X1 X1) X1
       grind)
    | exact resolve eq401 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq401
  have eq539 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq411 X0 (τ X1)
       grind)
    | exact superpose eq411 eq17
    | (have j1 := eq411 X0 (τ X1)
       grind)
    | exact resolve eq17 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq546 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq411 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq539 (τ X0) X1
       grind)
    | exact superpose eq539 eq18
    | (have j1 := eq539 (τ X0) X1
       grind)
    | exact resolve eq18 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq539
  have eq1011 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1006 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1006
    | (have j0 := eq1006 X0 X1
       grind)
    | exact resolve eq1006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1024 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1011
    | (have j0 := eq1011 X0 X1
       grind)
    | exact resolve eq1011 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1027 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1024 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1024
    | (have j0 := eq1024 X0 X1
       grind)
    | exact resolve eq1024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1090 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1027 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1027
    | (have j0 := eq1027 X1 (σ X0)
       grind)
    | exact resolve eq1027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1417 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X0 X0
       have i₂ := eq411 X0 (σ X0)
       grind)
    | exact superpose eq411 eq1090
    | (have j0 := eq1090 X1 X0
       have j1 := eq411 X0 (σ X1)
       grind)
    | exact resolve eq1090 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq1090
  have eq1447 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1417 X0 X1
       have j1 := eq546 (σ X1) X0
       grind)
    | (have r₁ := eq1417 X1 X1
       have r₂ := eq546 (σ X1) X1
       grind)
    | exact resolve eq1417 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq1417
  have eq1587 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1447 (σ X0) X1
       grind)
    | exact superpose eq1447 eq22
    | (have j1 := eq1447 (σ X0) X1
       grind)
    | exact resolve eq22 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1447
  have eq1594 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1587 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1587
    | (have j0 := eq1587 X0 X1
       grind)
    | exact resolve eq1587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1610 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1594 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1594
    | (have j0 := eq1594 X0 X1
       grind)
    | exact resolve eq1594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1619 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1610 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1610
    | (have j0 := eq1610 X0 X1
       grind)
    | exact resolve eq1610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1619 x y
       grind)
    | exact superpose eq1619 eq16
    | (have j1 := eq1619 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1619 x y
       grind)
    | exact resolve eq16 eq1619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1731 : x = (k y x) := by grind
  clear eq1706
  have eq2061 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq410
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq410
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq410 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2062 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq2061
  have eq2063 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2062
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2062 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2064 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2063
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2063
    | exact resolve eq2063 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063
  have eq2065 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2064
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2064
    | exact resolve eq2064 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064
  have eq2066 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq410
       have i₂ := eq2065
       grind)
    | exact superpose eq2065 eq410
    | exact resolve eq410 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq2065
  have eq2076 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2066
  have eq2077 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2076
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2076
    | exact resolve eq2076 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076
  have eq2078 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2077
  have eq2080 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2078
       grind)
    | exact superpose eq2078 eq16
    | exact resolve eq16 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq2101 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2080
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq2080
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq2080 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2102 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq2101
  have eq2104 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2102
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2105 : x = (M.op x y) := by
    first
    | (have i₁ := eq2104
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq2104
    | exact resolve eq2104 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731 eq2104
  have eq2106 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2080
       have i₂ := eq2105
       grind)
    | exact superpose eq2105 eq2080
    | exact resolve eq2080 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080 eq2105
  have eq2118 : False := by grind
  exact eq2118
