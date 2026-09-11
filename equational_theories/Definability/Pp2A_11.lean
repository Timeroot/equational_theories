import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq87 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq88 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11257
    | exact resolve eq11257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11257
  have eq11269 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11258
       have r₂ := eq28
       grind)
    | exact resolve eq11258 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11258
  have eq11273 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11269
    | exact resolve eq11269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11269
  have eq11278 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11273 eq88
    | (have r₁ := eq88
       have r₂ := eq11273
       grind)
    | exact resolve eq88 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq11273
  have eq11348 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11278
  have eq11349 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11348
  have eq11387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11349 eq78
    | exact resolve eq78 eq11349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq11349
  have eq11396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11387
  have eq11399 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11396
       have r₂ := eq28
       grind)
    | exact resolve eq11396 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11396
  have eq11401 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq11399
       grind)
    | exact superpose eq11399 eq52
    | exact resolve eq52 eq11399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq11403 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11399
       grind)
    | exact superpose eq11399 eq87
    | (have r₁ := eq87
       have r₂ := eq11399
       grind)
    | exact resolve eq87 eq11399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq11399
  have eq11473 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq11403
  have eq11474 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11473
  have eq11504 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11401
    | exact resolve eq11401 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11401
  have eq11739 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq11474
       grind)
    | exact superpose eq11474 eq49
    | exact resolve eq49 eq11474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11474
  have eq11755 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11739
    | exact resolve eq11739 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11739
  have eq11874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11755 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq11755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11755
  have eq11875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11874
  have eq11879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11875
    | exact resolve eq11875 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875
  have eq11890 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11879
       have r₂ := eq28
       grind)
    | exact resolve eq11879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11879
  have eq11894 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11890
    | exact resolve eq11890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11890
  have eq11907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11894 eq11504
    | exact resolve eq11504 eq11894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11504 eq11894
  have eq11972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11907
  have eq12005 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11972
       have r₂ := eq28
       grind)
    | exact resolve eq11972 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11972
  have eq12010 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12005 eq30
    | exact resolve eq30 eq12005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12005
  have eq12117 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12010
    | exact resolve eq12010 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12010
  have eq12118 : x = y := by grind
  clear eq12117
  have eq12136 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12118
       grind)
    | exact superpose eq12118 eq19
    | exact resolve eq19 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq12137 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq12118
       grind)
    | exact superpose eq12118 eq25
    | exact resolve eq25 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12118
  have eq12248 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12137
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12137
    | exact resolve eq12137 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12137
  have eq12265 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12248 eq27
    | exact resolve eq27 eq12248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12248
  have eq13106 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12265 eq69
    | exact resolve eq69 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq12265
  have eq13221 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13106
       have i₂ := eq12136
       grind)
    | exact superpose eq12136 eq13106
    | exact resolve eq13106 eq12136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12136 eq13106
  have eq13232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13221 eq15
    | exact resolve eq15 eq13221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13221
  have eq13276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13232
    | exact resolve eq13232 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq13232
  have eq13285 : False := by grind
  exact eq13285

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq341 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq52 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq14 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq55 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq55 X2 X2 X2 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq52 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq65
  have eq676 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X0
       have i₂ := eq341 X0 (σ X0)
       grind)
    | (have i₁ := eq75 X0 X0
       have i₂ := eq341 (σ X0) X1
       grind)
    | exact superpose eq341 eq75
    | exact resolve eq75 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq705 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq791 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x
       have i₂ := eq342 x X0 X1
       grind)
    | (have i₁ := eq53 (M.op x x)
       have i₂ := eq342 X0 x x
       grind)
    | exact superpose eq342 eq53
    | exact resolve eq53 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X5 X3)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq55 X5 x X3 X2
       have i₂ := eq342 x X0 X1
       grind)
    | (have i₁ := eq55 X0 (M.op X2 X2) X2 X3
       have i₂ := eq342 X0 X2 X2
       grind)
    | exact superpose eq342 eq55
    | exact resolve eq55 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq342
  have eq5446 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq343 X1 x X2 x
       have i₂ := eq425 X1 x X2 x X0
       grind)
    | exact superpose eq425 eq343
    | exact resolve eq343 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq5934 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5446 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq343 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq343 eq5446
    | exact resolve eq5446 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq5446
  have eq6756 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5934 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq5934
    | (have j0 := eq5934 x X0 y
       grind)
    | exact resolve eq5934 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6757 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq27 eq5934
    | (have j0 := eq5934 (σ x) X0 (σ y)
       grind)
    | exact resolve eq5934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5934
  have eq23763 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq705 X0 (τ X1)
       grind)
    | exact superpose eq705 eq35
    | (have j1 := eq705 X0 (τ X1)
       grind)
    | exact resolve eq35 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq23824 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq705 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq23855 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23763 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq23763
    | (have j0 := eq23763 X0 X1
       grind)
    | exact resolve eq23763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23763
  have eq23917 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23855 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq23855
    | (have j0 := eq23855 X0 X1
       grind)
    | exact resolve eq23855 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23855
  have eq25749 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq23917 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq33847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq33846
    | exact resolve eq33846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33846
  have eq33858 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq33847
       have r₂ := eq28
       grind)
    | exact resolve eq33847 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33847
  have eq33866 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq33875 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq33858 eq341
    | exact resolve eq341 eq33858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33978 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq33858
  have eq37892 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33866 eq103
    | exact resolve eq103 eq33866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33866
  have eq57538 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq37892
       have i₂ := eq33875 sF3
       grind)
    | exact superpose eq33875 eq37892
    | exact resolve eq37892 eq33875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33875 eq37892
  have eq57607 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq57538
  have eq57641 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq57607
       have r₂ := eq33978
       grind)
    | exact resolve eq57607 eq33978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33978 eq57607
  have eq57647 : y = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq57641
    | exact resolve eq57641 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57641
  have eq57650 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq25749 (σ y) (σ x)
       grind)
    | (have r₁ := eq57647
       have r₂ := eq25749 x y
       grind)
    | exact resolve eq57647 eq25749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25749 eq57647
  have eq57654 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq57650
       have i₂ := eq341 X0 sF3
       grind)
    | (have i₁ := eq57650
       have i₂ := eq341 sF3 x
       grind)
    | exact superpose eq341 eq57650
    | exact resolve eq57650 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57730 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq57650 eq550
    | exact resolve eq550 eq57650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57650
  have eq58094 : ∀ X1 : G, (σ x) = (k X1 X1) ∨ (σ x) = X1 ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    intro X1
    first
    | (have i₁ := eq23917 x X1
       have i₂ := eq57654 x
       grind)
    | (have i₁ := eq23917 y X1
       have i₂ := eq57654 x
       grind)
    | exact superpose eq57654 eq23917
    | (have j0 := eq23917 y x
       grind)
    | exact resolve eq23917 eq57654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58293 : x ≠ (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  have eq58294 : y ≠ (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  have eq62629 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq58094 x
       grind)
    | exact superpose eq58094 eq44
    | (have j1 := eq58094 x
       grind)
    | exact resolve eq44 eq58094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62639 : (k (σ y) (σ y)) = (σ (σ x)) ∨ y = (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq58094 y
       grind)
    | exact superpose eq58094 eq73
    | (have j1 := eq58094 y
       grind)
    | exact resolve eq73 eq58094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58094
  have eq62743 : (k (σ y) (σ y)) = (σ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq62639
       have r₂ := eq58294
       grind)
    | exact resolve eq62639 eq58294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58294 eq62639
  have eq62752 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq62629
       have r₂ := eq58293
       grind)
    | exact resolve eq62629 eq58293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62629
  have eq62842 : (k y y) = (τ (σ (σ x))) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq62743 eq103
    | exact resolve eq103 eq62743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62743
  have eq62914 : (σ x) = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62842
       have i₂ := eq16 sF2
       grind)
    | exact superpose eq16 eq62842
    | exact resolve eq62842 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62842
  have eq63019 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq62752 eq57730
    | exact resolve eq57730 eq62752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57730 eq62752
  have eq63049 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq63019
  have eq63322 : (σ x) = (σ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq63049 eq57654
    | exact resolve eq57654 eq63049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57654 eq63049
  have eq63348 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq63322
  have eq63409 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op X0 X0) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq63348
       have i₂ := eq341 X0 y
       grind)
    | (have i₁ := eq63348
       have i₂ := eq341 y x
       grind)
    | exact superpose eq341 eq63348
    | exact resolve eq63348 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63423 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (σ x)) := by grind
  have eq63432 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op y y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq341 X0 y
       have i₂ := eq63348
       grind)
    | exact superpose eq63348 eq341
    | exact resolve eq341 eq63348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63348
  have eq64026 : ∀ X0 : G, x ≠ y ∨ x = (M.op X0 X0) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have j0 := eq63409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63409
  have eq66199 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq63423
       grind)
    | exact superpose eq63423 eq73
    | exact resolve eq73 eq63423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63423
  have eq79777 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq66199
       have i₂ := eq63432 y
       grind)
    | exact superpose eq63432 eq66199
    | exact resolve eq66199 eq63432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66199
  have eq79859 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y y) := by grind
  clear eq79777
  have eq79898 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq64026 y
       grind)
    | (have r₁ := eq79859
       have r₂ := eq64026 x
       grind)
    | exact resolve eq79859 eq64026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64026 eq79859
  have eq79905 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79898
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq79898
    | exact resolve eq79898 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79898
  have eq79983 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq79905 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq79905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79905
  have eq79984 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y y) := by grind
  clear eq79983
  have eq80241 : y = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq79984 eq63432
    | exact resolve eq63432 eq79984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63432 eq79984
  have eq80288 : x = (M.op y y) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq80241
  have eq81193 : ∀ X0 : G, x = (M.op X0 X0) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq80288
       have i₂ := eq341 X0 y
       grind)
    | (have i₁ := eq80288
       have i₂ := eq341 y X0
       grind)
    | exact superpose eq341 eq80288
    | exact resolve eq80288 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81270 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq550 X0 y
       have i₂ := eq80288
       grind)
    | exact superpose eq80288 eq550
    | exact resolve eq550 eq80288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80288
  have eq81661 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    intro X1
    first
    | (have i₁ := eq23917 x X1
       have i₂ := eq81193 x
       grind)
    | exact superpose eq81193 eq23917
    | exact resolve eq23917 eq81193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23917
  have eq86487 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq81270 x
       grind)
    | exact superpose eq81270 eq44
    | exact resolve eq44 eq81270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq81270
  have eq96135 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq86487
       have i₂ := eq81193 x
       grind)
    | exact superpose eq81193 eq86487
    | exact resolve eq86487 eq81193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81193 eq86487
  have eq96219 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq96135
  have eq96263 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq96219
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96219
    | exact resolve eq96219 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96219
  have eq96333 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (M.op X0 X0) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | exact superpose eq96263 eq23824
    | (have j0 := eq23824 X0 (σ x)
       grind)
    | exact resolve eq23824 eq96263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96339 : x = (σ x) ∨ x = (σ x) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq96263 eq81661
    | (have j0 := eq81661 (σ x)
       grind)
    | exact resolve eq81661 eq96263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81661
  have eq96342 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq96263 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq96263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96263
  have eq96343 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq96342
  have eq96346 : (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ x = (σ x) := by grind
  clear eq96339
  have eq96351 : ∀ X0 : G, (M.op X0 X0) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have j0 := eq96333 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96333
  have eq96395 : (σ x) = (τ (σ x)) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq96346 eq16
    | exact resolve eq16 eq96346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96346
  have eq96467 : x = (σ x) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq96395
    | exact resolve eq96395 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96395
  have eq96468 : y = (σ y) ∨ x = (σ x) := by grind
  clear eq96467
  have eq96486 : (k y y) = (τ (k y y)) ∨ x = (σ x) := by
    first
    | exact superpose eq96468 eq103
    | exact resolve eq103 eq96468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq96468
  have eq97166 : (σ x) = (τ (σ x)) ∨ x = (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq96486
       have i₂ := eq62914
       grind)
    | exact superpose eq62914 eq96486
    | exact resolve eq96486 eq62914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62914 eq96486
  have eq97241 : (σ x) = (τ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq97166
       have r₂ := eq58293
       grind)
    | exact resolve eq97166 eq58293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97166
  have eq97243 : x = (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq97241
    | exact resolve eq97241 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97241
  have eq97245 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq97243
       have r₂ := eq58293
       grind)
    | exact resolve eq97243 eq58293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58293 eq97243
  have eq97353 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq97245
       have i₂ := eq341 X0 y
       grind)
    | (have i₁ := eq97245
       have i₂ := eq341 y x
       grind)
    | exact superpose eq341 eq97245
    | exact resolve eq97245 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97385 : (k y y) = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq97394 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq341 X0 y
       have i₂ := eq97245
       grind)
    | exact superpose eq97245 eq341
    | exact resolve eq341 eq97245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97439 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq550 X0 y
       have i₂ := eq97245
       grind)
    | exact superpose eq97245 eq550
    | exact resolve eq550 eq97245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97245
  have eq98218 : ∀ X0 : G, x ≠ y ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq97353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97353
  have eq105679 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq97385
       grind)
    | exact superpose eq97385 eq73
    | exact resolve eq73 eq97385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq97385
  have eq106002 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq97439 x
       grind)
    | exact superpose eq97439 eq72
    | exact resolve eq72 eq97439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq106086 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq106002
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106002
    | exact resolve eq106002 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106002
  have eq106118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq106086
    | exact resolve eq106086 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq106086
  have eq152758 : (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) ∨ y = (σ y) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq96343
       have i₂ := eq96351 sF2
       grind)
    | exact superpose eq96351 eq96343
    | exact resolve eq96343 eq96351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96343 eq96351
  have eq152797 : (σ x) = (σ (σ x)) ∨ y = (σ y) := by grind
  clear eq152758
  have eq152992 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (σ x)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq152797 eq225
    | exact resolve eq225 eq152797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152997 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (σ x) (τ X0)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq152797 eq326
    | exact resolve eq326 eq152797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152797
  have eq154354 : ∀ X0 : G, (k X0 (σ x)) = (τ (k (σ X0) (σ x))) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq152992 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq152992
    | exact resolve eq152992 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152992
  have eq154631 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (τ (σ x))) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq154354 X0
       have i₂ := eq326 X0 sF2
       grind)
    | exact superpose eq326 eq154354
    | exact resolve eq154354 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq154354
  have eq154697 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq29 eq154631
    | exact resolve eq154631 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154631
  have eq156865 : ∀ X0 : G, (k (σ x) X0) = (τ (k (σ x) (σ X0))) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq152997 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq152997
    | exact resolve eq152997 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152997
  have eq157116 : ∀ X0 : G, (k (σ x) X0) = (k (τ (σ x)) X0) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq156865 x
       have i₂ := eq225 sF2 x
       grind)
    | exact superpose eq225 eq156865
    | exact resolve eq156865 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq156865
  have eq157158 : ∀ X0 : G, (k x X0) = (k (σ x) X0) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq29 eq157116
    | exact resolve eq157116 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq157116
  have eq206974 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq105679
       have i₂ := eq97394 y
       grind)
    | exact superpose eq97394 eq105679
    | exact resolve eq105679 eq97394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105679
  have eq207120 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq98218 y
       grind)
    | (have r₁ := eq206974
       have r₂ := eq98218 x
       grind)
    | exact resolve eq206974 eq98218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98218 eq206974
  have eq207132 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq207120
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq207120
    | exact resolve eq207120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207120
  have eq208119 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq207132 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq207132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207132
  have eq208120 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq208119
  have eq209255 : y = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq208120 eq97394
    | exact resolve eq97394 eq208120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97394 eq208120
  have eq209298 : x = (M.op y y) ∨ y = (σ y) := by grind
  clear eq209255
  have eq209391 : ∀ X0 : G, x = (M.op X0 X0) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq209298
       have i₂ := eq341 X0 y
       grind)
    | (have i₁ := eq209298
       have i₂ := eq341 y X0
       grind)
    | exact superpose eq341 eq209298
    | exact resolve eq209298 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209481 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq550 X0 y
       have i₂ := eq209298
       grind)
    | exact superpose eq209298 eq550
    | exact resolve eq550 eq209298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209574 : y = (M.op (M.op x y) (M.op x x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq6756 y
       have i₂ := eq209298
       grind)
    | exact superpose eq209298 eq6756
    | exact resolve eq6756 eq209298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209575 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq6757 y
       have i₂ := eq209298
       grind)
    | exact superpose eq209298 eq6757
    | exact resolve eq6757 eq209298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6757 eq209298
  have eq218599 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq209481 sF0
       grind)
    | exact superpose eq209481 eq46
    | exact resolve eq46 eq209481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218636 : (k x x) = (M.op (σ x) x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq154697 x
       have i₂ := eq209481 sF2
       grind)
    | exact superpose eq209481 eq154697
    | exact resolve eq154697 eq209481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154697
  have eq218643 : (k x x) = (M.op (σ x) x) ∨ y = (σ y) := by grind
  clear eq218636
  have eq219625 : y = (M.op (M.op x y) x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq209574
       have i₂ := eq209391 x
       grind)
    | exact superpose eq209391 eq209574
    | exact resolve eq209574 eq209391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209574
  have eq219669 : y = (M.op (M.op x y) x) ∨ y = (σ y) := by grind
  clear eq219625
  have eq219707 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) y) (M.op x y)) (M.op X1 x)) = X1 ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq219669 eq443
    | exact resolve eq443 eq219669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219714 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) x) = (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X2)) y) (M.op x y)) ∨ y = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq219669 eq793
    | exact resolve eq793 eq219669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq219727 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq791 eq219714
    | exact resolve eq219714 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq219714
  have eq219730 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq53 eq219707
    | exact resolve eq219707 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq219707
  have eq222795 : (M.op x x) = (M.op (σ x) x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq209481 x
       have i₂ := eq218643
       grind)
    | exact superpose eq218643 eq209481
    | exact resolve eq209481 eq218643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218643
  have eq222832 : (M.op x x) = (M.op (σ x) x) ∨ y = (σ y) := by grind
  clear eq222795
  have eq230217 : (σ x) = (M.op x (M.op x x)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq222832 eq219730
    | exact resolve eq219730 eq222832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219730 eq222832
  have eq230243 : (σ x) = (M.op x (M.op x x)) ∨ y = (σ y) := by grind
  clear eq230217
  have eq235635 : (σ x) = (M.op x x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq230243
       have i₂ := eq209391 x
       grind)
    | exact superpose eq209391 eq230243
    | exact resolve eq230243 eq209391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209391 eq230243
  have eq235705 : (σ x) = (M.op x x) ∨ y = (σ y) := by grind
  clear eq235635
  have eq236058 : x = (M.op (σ x) x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq219727 x
       have i₂ := eq235705
       grind)
    | exact superpose eq235705 eq219727
    | exact resolve eq219727 eq235705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219727 eq235705
  have eq236082 : x = (M.op (σ x) x) ∨ y = (σ y) := by grind
  clear eq236058
  have eq238214 : (σ y) = (M.op (M.op (σ x) (σ y)) x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq236082 eq209575
    | exact resolve eq209575 eq236082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209575 eq236082
  have eq238251 : (σ y) = (M.op (M.op (σ x) (σ y)) x) ∨ y = (σ y) := by grind
  clear eq238214
  have eq244310 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) (M.op X1 x)) = X1 ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq238251 eq443
    | exact resolve eq443 eq238251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq238251
  have eq244333 : ∀ X1 : G, (M.op (σ x) (M.op X1 x)) = X1 ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq54 eq244310
    | exact resolve eq244310 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq244310
  have eq450540 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq219669 eq218599
    | exact resolve eq218599 eq219669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218599 eq219669
  have eq450679 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (σ y) := by grind
  clear eq450540
  have eq450683 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (σ y) := by
    first
    | (have i₁ := eq450679
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq450679
    | exact resolve eq450679 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450679
  have eq450707 : (σ y) = (k x (σ (M.op x y))) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq450683 eq157158
    | exact resolve eq157158 eq450683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157158 eq450683
  have eq450716 : (σ y) = (k x (σ (M.op x y))) ∨ y = (σ y) := by grind
  clear eq450707
  have eq450747 : (σ y) = (M.op (σ (M.op x y)) x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq450716 eq209481
    | exact resolve eq209481 eq450716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209481 eq450716
  have eq450756 : (σ y) = (M.op (σ (M.op x y)) x) ∨ y = (σ y) := by grind
  clear eq450747
  have eq453034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq450756 eq244333
    | exact resolve eq244333 eq450756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244333 eq450756
  have eq453075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq453034
  have eq453076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq27 eq453075
    | exact resolve eq453075 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453075
  have eq453077 : y = (σ y) := by
    first
    | (have r₁ := eq453076
       have r₂ := eq28
       grind)
    | exact resolve eq453076 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453076
  have eq453863 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq453077 eq27
    | exact resolve eq27 eq453077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq454140 : (σ (M.op x y)) = (k y (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq453077 eq106118
    | exact resolve eq106118 eq453077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106118
  have eq462049 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq454140 eq97439
    | exact resolve eq97439 eq454140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97439 eq454140
  have eq462056 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (M.op y y) := by grind
  clear eq462049
  have eq462064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq453863 eq462056
    | exact resolve eq462056 eq453863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462056
  have eq462080 : x = (M.op y y) := by
    first
    | (have r₁ := eq462064
       have r₂ := eq28
       grind)
    | exact resolve eq462064 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462064
  have eq462097 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq462080
       have i₂ := eq341 X0 y
       grind)
    | (have i₁ := eq462080
       have i₂ := eq341 y X0
       grind)
    | exact superpose eq341 eq462080
    | exact resolve eq462080 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq462209 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq550 X0 y
       have i₂ := eq462080
       grind)
    | exact superpose eq462080 eq550
    | exact resolve eq550 eq462080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq462080
  have eq463285 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq6756 x
       have i₂ := eq462097 x
       grind)
    | exact superpose eq462097 eq6756
    | exact resolve eq6756 eq462097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6756
  have eq464453 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq463285
       have i₂ := eq462097 x
       grind)
    | exact superpose eq462097 eq463285
    | exact resolve eq463285 eq462097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463285
  have eq466208 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23824 X0 x
       have i₂ := eq462209 x
       grind)
    | exact superpose eq462209 eq23824
    | (have j0 := eq23824 X0 x
       grind)
    | exact resolve eq23824 eq462209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23824
  have eq466437 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq462209 sF0
       grind)
    | exact superpose eq462209 eq46
    | exact resolve eq46 eq462209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq466514 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq464453 eq466437
    | exact resolve eq466437 eq464453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464453 eq466437
  have eq466661 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq466208 X0
       have i₂ := eq462097 x
       grind)
    | exact superpose eq462097 eq466208
    | (have j0 := eq466208 X0
       grind)
    | exact resolve eq466208 eq462097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466208
  have eq466662 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq466661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466661
  have eq466709 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq466514
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq466514
    | exact resolve eq466514 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq466514
  have eq466787 : x = (σ x) := by
    first
    | (have i₁ := eq466662 x
       have i₂ := eq462097 x
       grind)
    | exact superpose eq462097 eq466662
    | exact resolve eq466662 eq462097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466662
  have eq466825 : y = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq453077 eq466709
    | exact resolve eq466709 eq453077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453077 eq466709
  have eq466849 : x = (σ x) := by
    first
    | (have i₁ := eq466787
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq466787
    | exact resolve eq466787 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq466787
  have eq467391 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq466849 eq453863
    | exact resolve eq453863 eq466849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453863
  have eq467405 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq467391
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq467391
    | exact resolve eq467391 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467391
  have eq467734 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq467405 eq28
    | exact resolve eq28 eq467405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq467405
  have eq469003 : y = (k x (σ (M.op x y))) := by
    first
    | exact superpose eq466849 eq466825
    | exact resolve eq466825 eq466849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466825 eq466849
  have eq469004 : y = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq469003
       have i₂ := eq462209 sF1
       grind)
    | exact superpose eq462209 eq469003
    | exact resolve eq469003 eq462209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462209 eq469003
  have eq469012 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) x) y) := by
    intro X0
    first
    | exact superpose eq469004 eq14
    | exact resolve eq14 eq469004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469004
  have eq469085 : (σ (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq469012 x
       have i₂ := eq462097 x
       grind)
    | exact superpose eq462097 eq469012
    | exact resolve eq469012 eq462097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469012
  have eq469117 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq469085
       have i₂ := eq462097 x
       grind)
    | exact superpose eq462097 eq469085
    | exact resolve eq469085 eq462097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462097 eq469085
  have eq469145 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq469117
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq469117
    | exact resolve eq469117 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq469117
  have eq469163 : False := by grind
  exact eq469163

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq559 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq539 X1 X0
       grind)
    | exact superpose eq539 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq539 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq539 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X2 X0
       grind)
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq559 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq957 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq564 X2 X1 X0
       have i₂ := eq930 X0 X1
       grind)
    | exact superpose eq930 eq564
    | exact resolve eq564 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq958 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq930 X0 X1
       grind)
    | exact superpose eq930 eq16
    | exact resolve eq16 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1464 : (M.op y y) = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1465 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1538 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1538 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1538 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1538 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1661 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq1543 X0
       grind)
    | exact superpose eq1543 eq539
    | exact resolve eq539 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1678 : ∀ X0 X1 X2 : G, (M.op (k X1 (M.op X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X1 X2 X0
       have i₂ := eq1543 X0
       grind)
    | exact superpose eq1543 eq957
    | exact resolve eq957 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1679 : ∀ X0 X1 X2 : G, (M.op (k X1 (k X0 X0)) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq958 X1 X0 X2
       have i₂ := eq1543 X0
       grind)
    | exact superpose eq1543 eq958
    | exact resolve eq958 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1712 : ∀ X0 X1 X2 : G, (M.op (k X1 (k X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1678 X0 X1 X2
       have i₂ := eq1543 X2
       grind)
    | exact superpose eq1543 eq1678
    | exact resolve eq1678 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq5522 : ∀ X0 : G, (M.op y x) = (k X0 X0) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1661 X0 y
       have i₂ := eq1464
       grind)
    | exact superpose eq1464 eq1661
    | exact resolve eq1661 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq5597 : ∀ X0 : G, (M.op (σ y) (σ x)) = (k X0 X0) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1465 eq1661
    | exact resolve eq1661 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465 eq1661
  have eq15467 : ∀ X0 X1 : G, y = (M.op (k x (k X1 X1)) (k X0 X0)) ∨ (M.op x y) = (k y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1679 X1 x y
       have i₂ := eq5522 X0
       grind)
    | exact superpose eq5522 eq1679
    | exact resolve eq1679 eq5522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522
  have eq15665 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq15467 x x
       have i₂ := eq1712 x x x
       grind)
    | exact superpose eq1712 eq15467
    | exact resolve eq15467 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15467
  have eq15711 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq15665
       grind)
    | exact superpose eq15665 eq40
    | exact resolve eq40 eq15665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15665
  have eq15712 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq15711
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15711
    | exact resolve eq15711 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15711
  have eq15714 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq15712
    | exact resolve eq15712 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq15756 : ∀ X0 X1 : G, (σ y) = (M.op (k (σ x) (k X1 X1)) (k X0 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq5597 eq1679
    | exact resolve eq1679 eq5597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679 eq5597
  have eq15956 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f15956_12 : ∀ X0 X1 : G, (σ y) = (M.op (k (σ x) (k X1 X1)) (k X0 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
      intro X0 X1
      grind
    have f15956_13 : ∀ X0 X1 X2 : G, (M.op (k X1 (k X2 X2)) (k X0 X0)) = X1 := by
      intro X0 X1 X2
      grind
    have f15956_21 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by grind
    have f15956_22 : (σ y) ≠ (σ x) := by grind
    have f15956_24 : ∀ X0 X1 : G, (σ y) = (M.op (k (σ x) (k X1 X1)) (k X0 X0)) := by
      intro X0 X1
      first
      | (have j0 := f15956_12 X0 X1
         grind)
      | (have r₁ := f15956_12 X0 X1
         have r₂ := f15956_21
         grind)
      | exact resolve f15956_12 f15956_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15956_25 : (σ y) = (σ x) := by
      first
      | (have i₁ := f15956_24 x x
         have i₂ := f15956_13 x (σ x) x
         grind)
      | exact superpose f15956_13 f15956_24
      | exact resolve f15956_24 f15956_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15956_26 : False := by
      first
      | (have r₁ := f15956_25
         have r₂ := f15956_22
         grind)
      | exact resolve f15956_25 f15956_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f15956_26
  clear eq1712 eq15756
  have eq16005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15956 eq15714
    | exact resolve eq15714 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15714 eq15956
  have eq16011 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16005
       have r₂ := eq27
       grind)
    | exact resolve eq16005 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16005
  have eq16014 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16011 eq32
    | exact resolve eq32 eq16011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq16011
  have eq16044 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq16014
    | exact resolve eq16014 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16014
  have eq16045 : x = y := by grind
  clear eq16044
  have eq16049 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16045
       grind)
    | exact superpose eq16045 eq18
    | exact resolve eq18 eq16045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq16050 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16045
       grind)
    | exact superpose eq16045 eq24
    | exact resolve eq24 eq16045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16045
  have eq16067 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16050
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16050
    | exact resolve eq16050 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16050
  have eq16068 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq16049
       have i₂ := eq1543 x
       grind)
    | exact superpose eq1543 eq16049
    | exact resolve eq16049 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16049
  have eq16070 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16067 eq26
    | exact resolve eq26 eq16067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq16067
  have eq16101 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16070
       have i₂ := eq1543 sF2
       grind)
    | exact superpose eq1543 eq16070
    | exact resolve eq16070 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543 eq16070
  have eq16108 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq16068
       grind)
    | exact superpose eq16068 eq40
    | exact resolve eq40 eq16068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16068
  have eq16245 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16108
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16108
    | exact resolve eq16108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16108
  have eq16275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16101 eq16245
    | exact resolve eq16245 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101 eq16245
  have eq16290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16275
    | exact resolve eq16275 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16275
  have eq16301 : False := by grind
  exact eq16301

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq113 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X0) X2) X1) = (M.op X1 (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X2) X1
       have i₂ := eq14 (M.op X0 X0) X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) X2)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X2) X1
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq120 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq49
    | exact resolve eq49 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq120
    | exact resolve eq120 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq137 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq115 sF1
       grind)
    | exact superpose eq115 eq139
    | exact resolve eq139 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq142
    | exact resolve eq142 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq142
  have eq435 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq773 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq435 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq435 (M.op X0 X0) X1
       grind)
    | exact superpose eq435 eq64
    | (have r₁ := eq64 X1 (M.op X1 X1) X2
       have r₂ := eq435 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq64 X0 (M.op X0 X0) X2
       have r₂ := eq435 X0 (M.op X0 X0)
       grind)
    | exact resolve eq64 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq776 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq773 X0 x X2
       grind)
    | (have r₁ := eq773 X0 x X2
       have r₂ := eq435 X0 x
       grind)
    | (have r₁ := eq773 x X0 X2
       have r₂ := eq435 X0 x
       grind)
    | exact resolve eq773 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq973 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X2) X1) = (M.op X1 (M.op (M.op X0 X0) X2)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq113 X0 X1 X2
       grind)
    | (have r₁ := eq113 X0 X1 X2
       have r₂ := eq435 X0 X1
       grind)
    | (have r₁ := eq113 X1 X0 X2
       have r₂ := eq435 X0 X1
       grind)
    | exact resolve eq113 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1175 : ∀ X0 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq973 (M.op x x) x (M.op X0 (M.op x x))
       have i₂ := eq14 X0 x (M.op x x)
       grind)
    | exact superpose eq14 eq973
    | (have j0 := eq973 X0 X2 X2
       grind)
    | exact resolve eq973 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1560 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1175 y x
       grind)
    | exact superpose eq1175 eq71
    | (have j1 := eq1175 x x
       grind)
    | exact resolve eq71 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1584 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1560
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1560
    | exact resolve eq1560 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1584
    | exact resolve eq1584 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1584
  have eq1590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1586 eq1175
    | (have j0 := eq1175 x (σ x)
       grind)
    | exact resolve eq1175 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq1586
  have eq1592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1590
    | exact resolve eq1590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1595 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1592
       have r₂ := eq27
       grind)
    | exact resolve eq1592 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1599 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1595 eq121
    | exact resolve eq121 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1595
  have eq1631 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1599
    | exact resolve eq1599 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1599
  have eq1632 : x = (M.op x x) := by grind
  clear eq1631
  have eq1633 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1632
       have i₂ := eq435 X0 x
       grind)
    | (have i₁ := eq1632
       have i₂ := eq435 x X0
       grind)
    | exact superpose eq435 eq1632
    | exact resolve eq1632 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq1659 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq776 x x
       have i₂ := eq1632
       grind)
    | exact superpose eq1632 eq776
    | exact resolve eq776 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq1632
  have eq1713 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X1
       have i₂ := eq1633 X1
       grind)
    | exact superpose eq1633 eq14
    | exact resolve eq14 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1724 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq1633 (M.op X0 X0)
       grind)
    | exact superpose eq1633 eq14
    | exact resolve eq14 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq1633 sF0
       grind)
    | exact superpose eq1633 eq145
    | exact resolve eq145 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1742 : x = (σ x) := by
    first
    | (have i₁ := eq1734
       have i₂ := eq1633 sF1
       grind)
    | exact superpose eq1633 eq1734
    | exact resolve eq1734 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1749 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq1724 x X1
       have i₂ := eq1633 x
       grind)
    | exact superpose eq1633 eq1724
    | exact resolve eq1724 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1754 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq1713 x X1
       have i₂ := eq1633 x
       grind)
    | exact superpose eq1633 eq1713
    | exact resolve eq1713 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633 eq1713
  have eq1775 : x = (σ x) := by
    first
    | (have i₁ := eq1742
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1742
    | exact resolve eq1742 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1742
  have eq1789 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1775 eq26
    | exact resolve eq26 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1935 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq137
       have i₂ := eq1659 sF0
       grind)
    | exact superpose eq1659 eq137
    | exact resolve eq137 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1943 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) x) := by
    first
    | exact superpose eq1775 eq1935
    | exact resolve eq1935 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775 eq1935
  have eq1950 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq1943
       have i₂ := eq1659 sF1
       grind)
    | exact superpose eq1659 eq1943
    | exact resolve eq1943 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659 eq1943
  have eq1997 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1754 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1754
    | (have j0 := eq1754 y
       grind)
    | exact resolve eq1754 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1754
  have eq2136 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq1997 eq1950
    | exact resolve eq1950 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950 eq1997
  have eq2137 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq2136
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2136
    | exact resolve eq2136 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2136
  have eq2138 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq2137 eq1749
    | exact resolve eq1749 eq2137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749 eq2137
  have eq2143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1789 eq2138
    | exact resolve eq2138 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq2138
  have eq2146 : False := by grind
  exact eq2146

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq72
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq72 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq102
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq114
  have eq124 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq393 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq52 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq91
    | (have j0 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq91 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq691
    | exact resolve eq691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq695 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq692
       have r₂ := eq28
       grind)
    | exact resolve eq692 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq697 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq695
       have i₂ := eq393 X0 sF2
       grind)
    | (have i₁ := eq695
       have i₂ := eq393 sF2 x
       grind)
    | exact superpose eq393 eq695
    | exact resolve eq695 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq734 : y ≠ (σ y) ∨ y = (M.op x x) := by grind
  have eq745 : ∀ X0 X1 X3 : G, (M.op X1 X1) ≠ X0 ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq65 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1))) x
       have i₂ := eq52 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq52 eq65
    | (have r₁ := eq65 X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X1))) x
       have r₂ := eq52 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq746 : ∀ X0 X1 : G, (σ y) ≠ (M.op X0 X0) ∨ (M.op (σ y) X1) = (k X1 (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (M.op X0 X0) x
       have i₂ := eq697 (M.op X0 X0)
       grind)
    | exact superpose eq697 eq65
    | exact resolve eq65 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq751 : ∀ X1 : G, (M.op (σ y) X1) = (k X1 (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have j0 := eq746 x X1
       grind)
    | (have r₁ := eq746 x X1
       have r₂ := eq697 x
       grind)
    | exact resolve eq746 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq873 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq751 eq85
    | exact resolve eq85 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq751
  have eq1095 : (τ (σ y)) = (k y y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq873
       have i₂ := eq697 sF3
       grind)
    | exact superpose eq697 eq873
    | exact resolve eq873 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1110 : (τ (σ y)) = (k y y) ∨ y = (M.op x x) := by grind
  clear eq1095
  have eq1112 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq1110
    | exact resolve eq1110 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1110
  have eq1115 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91 y y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq91
    | (have j0 := eq91 y y
       grind)
    | exact resolve eq91 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1116 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq1115
  have eq1165 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1116
       grind)
    | exact superpose eq1116 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1116
       grind)
    | exact resolve eq13 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180 : y = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq697 y
       have i₂ := eq1116
       grind)
    | exact superpose eq1116 eq697
    | exact resolve eq697 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq1116
  have eq1188 : y = (σ y) ∨ y = (M.op x x) := by grind
  clear eq1180
  have eq1189 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1191 : y = (M.op x x) := by
    first
    | (have r₁ := eq1188
       have r₂ := eq734
       grind)
    | exact resolve eq1188 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq1188
  have eq1192 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1189 X0
       have j1 := eq745 y x X0
       grind)
    | (have r₁ := eq1189 y
       have r₂ := eq745 (k y y) y x
       grind)
    | (have r₁ := eq1189 X0
       have r₂ := eq745 y x x
       grind)
    | exact resolve eq1189 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq1189
  have eq1195 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1191
       have i₂ := eq393 X0 x
       grind)
    | (have i₁ := eq1191
       have i₂ := eq393 x X0
       grind)
    | exact superpose eq393 eq1191
    | exact resolve eq1191 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq1191
  have eq1278 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq1195 x
       grind)
    | exact superpose eq1195 eq53
    | exact resolve eq53 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1300 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X1
       have i₂ := eq1195 X1
       grind)
    | exact superpose eq1195 eq14
    | exact resolve eq14 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X1 : G, (M.op (M.op y X1) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq1300 x X1
       have i₂ := eq1195 x
       grind)
    | exact superpose eq1195 eq1300
    | exact resolve eq1300 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1333 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1278
       have i₂ := eq1195 y
       grind)
    | exact superpose eq1195 eq1278
    | exact resolve eq1278 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1362 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1192 y
       grind)
    | exact superpose eq1192 eq73
    | exact resolve eq73 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1363 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq124
       have i₂ := eq1192 sF0
       grind)
    | exact superpose eq1192 eq124
    | exact resolve eq124 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1368 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1333 eq1363
    | exact resolve eq1363 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333 eq1363
  have eq1369 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1362
       have i₂ := eq1195 y
       grind)
    | exact superpose eq1195 eq1362
    | exact resolve eq1362 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1370 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1368
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1368
    | exact resolve eq1368 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1368
  have eq1371 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1369
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1369
    | exact resolve eq1369 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1369
  have eq1385 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1371 eq91
    | (have j0 := eq91 (σ y) (σ y)
       grind)
    | exact resolve eq91 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1371
  have eq1386 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1385
  have eq1388 : y = (σ y) := by
    first
    | (have i₁ := eq1386
       have i₂ := eq1195 sF3
       grind)
    | exact superpose eq1195 eq1386
    | exact resolve eq1386 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1386
  have eq1392 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1388 eq27
    | exact resolve eq27 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1412 : (σ x) = (k (σ (M.op x y)) y) := by
    first
    | exact superpose eq1388 eq1370
    | exact resolve eq1370 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq1388
  have eq1416 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq1412
       have i₂ := eq1192 sF1
       grind)
    | exact superpose eq1192 eq1412
    | exact resolve eq1412 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192 eq1412
  have eq1699 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1416 eq1322
    | exact resolve eq1322 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq1416
  have eq1733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1392 eq1699
    | exact resolve eq1699 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq1699
  have eq1735 : False := by grind
  exact eq1735

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, x = (M.op (M.op (k X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (k X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (k X1 X1) X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq187
    | exact resolve eq187 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq445 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq323
    | exact resolve eq323 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq647 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X2 (M.op (M.op X1 X1) (k X2 X2))
       have i₂ := eq16 X0 X1 (k X2 X2)
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq647
    | exact resolve eq647 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X1 x x
       have i₂ := eq652 X0 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 : G, (k X2 X2) = (M.op (k X0 X0) (k X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X2 x (k X2 X2)
       have i₂ := eq652 (M.op (k X2 X2) x) X0 X1
       grind)
    | exact superpose eq652 eq186
    | exact resolve eq186 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 (k X1 X1) x X2
       have i₂ := eq652 X0 X1 x
       grind)
    | (have i₁ := eq183 (k X1 X1) X1 X2
       have i₂ := eq652 (k X1 X1) X1 X2
       grind)
    | exact superpose eq652 eq183
    | exact resolve eq183 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq652
  have eq721 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) (M.op X2 (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq714 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq714
    | exact resolve eq714 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X0 X2
       grind)
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X2 X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq698 X0 (M.op (k X1 X1) x)
       grind)
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq698 (M.op (k X1 X1) x) X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq806 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq762 (M.op (k X1 X1) x) X0
       grind)
    | exact superpose eq762 eq186
    | exact resolve eq186 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq762 X0 (σ X1)
       grind)
    | exact superpose eq762 eq10
    | exact resolve eq10 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X1 (σ X1)
       have i₂ := eq762 X0 (σ X1)
       grind)
    | exact superpose eq762 eq380
    | exact resolve eq380 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq827 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X1 X1
       have i₂ := eq762 X0 (τ X1)
       grind)
    | exact superpose eq762 eq445
    | exact resolve eq445 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq762 X0 (τ X1)
       grind)
    | exact superpose eq762 eq34
    | exact resolve eq34 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq762
  have eq829 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq828
    | exact resolve eq828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq830 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq826
    | exact resolve eq826 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq846 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq829
    | exact resolve eq829 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq847 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq830
    | exact resolve eq830 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq960 : ∀ X0 X2 : G, (σ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq825 x X2
       have i₂ := eq825 x X0
       grind)
    | exact superpose eq825 eq825
    | exact resolve eq825 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq825
    | exact resolve eq825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : ∀ X0 X2 : G, (τ (k X0 X0)) = (τ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq827 x X2
       have i₂ := eq827 x X0
       grind)
    | exact superpose eq827 eq827
    | exact resolve eq827 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1092 : ∀ X0 X2 : G, (τ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq825 x X2
       have i₂ := eq827 x X0
       grind)
    | exact superpose eq827 eq825
    | exact resolve eq825 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1102 : ∀ X0 X1 X2 : G, (M.op (τ (k X0 X0)) (M.op X2 (k X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X1 (k X1 X1) X2
       have i₂ := eq827 (k X1 X1) X0
       grind)
    | exact superpose eq827 eq186
    | exact resolve eq186 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1156 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq846 x X1
       have i₂ := eq846 X0 x
       grind)
    | exact superpose eq846 eq846
    | exact resolve eq846 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1286 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1286
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1286
    | exact resolve eq1286 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1289 : (M.op x y) = (k x y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1285
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1285
    | exact resolve eq1285 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1348 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq847 x X1
       have i₂ := eq847 X0 x
       grind)
    | exact superpose eq847 eq847
    | exact resolve eq847 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 X2 : G, (σ (σ (k X0 X0))) = (τ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq827 x X2
       have i₂ := eq969 X0 x
       grind)
    | exact superpose eq969 eq827
    | exact resolve eq827 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq969
  have eq1699 : ∀ X0 X1 : G, (τ (τ (k X0 X0))) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X1 x
       have i₂ := eq847 X0 x
       grind)
    | exact superpose eq847 eq1065
    | exact resolve eq1065 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq2047 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq960 X1 x
       have i₂ := eq1156 X0 x
       grind)
    | exact superpose eq1156 eq960
    | exact resolve eq960 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq1156
  have eq3317 : ∀ X0 X1 X3 : G, (k X1 X1) = (M.op (σ (k X0 X0)) (k X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq708 x X3 X1
       have i₂ := eq846 X0 x
       grind)
    | exact superpose eq846 eq708
    | exact resolve eq708 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq3632 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X0) = (M.op (k X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq721 X0 X1 (M.op (k X2 X2) X0)
       have i₂ := eq192 X0 X2
       grind)
    | exact superpose eq192 eq721
    | exact resolve eq721 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq721
  have eq3888 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (σ (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3632 X2 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3632
    | exact resolve eq3632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632
  have eq4232 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq40
    | exact resolve eq40 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1289
  have eq4233 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq4232
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4232
    | exact resolve eq4232 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232
  have eq4235 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq4233
    | exact resolve eq4233 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq13935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq4235 eq1288
    | exact resolve eq1288 eq4235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq13942 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq13935
       have r₂ := eq27
       grind)
    | exact resolve eq13935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13935
  have eq14033 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq13942 eq141
    | exact resolve eq141 eq13942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq13942
  have eq14269 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq14033
    | exact resolve eq14033 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14033
  have eq14270 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14269
  have eq14371 : ∀ X0 X1 : G, (M.op (M.op x X0) (k X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq773 X1 x X0
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq773
    | exact resolve eq773 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14373 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq806 X0 x
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq806
    | exact resolve eq806 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14376 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq846 x X0
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq846
    | exact resolve eq846 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq14401 : ∀ X0 : G, (σ x) = (τ (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1092 X0 x
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq1092
    | exact resolve eq1092 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq14427 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1622 x X0
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq1622
    | exact resolve eq1622 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq14436 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2047 x X0
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq2047
    | exact resolve eq2047 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq14444 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) (k X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq3317 x X0 X1
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq3317
    | exact resolve eq3317 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq14466 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq3888 x X0 X1
       have i₂ := eq14270
       grind)
    | exact superpose eq14270 eq3888
    | exact resolve eq3888 eq14270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3888 eq14270
  have eq14474 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq14466 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14466
    | (have j0 := eq14466 X0 X1
       grind)
    | exact resolve eq14466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14466
  have eq14483 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) (k X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq14444 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14444
    | (have j0 := eq14444 X0 X1
       grind)
    | exact resolve eq14444 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14444
  have eq14487 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14436 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14436
    | (have j0 := eq14436 X0
       grind)
    | exact resolve eq14436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14436
  have eq14494 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14427 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14427
    | (have j0 := eq14427 X0
       grind)
    | exact resolve eq14427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14427
  have eq14511 : ∀ X0 : G, (σ x) = (τ (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14401 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14401
    | (have j0 := eq14401 X0
       grind)
    | exact resolve eq14401 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14401
  have eq14535 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14376 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14376
    | (have j0 := eq14376 X0
       grind)
    | exact resolve eq14376 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14376
  have eq14538 : ∀ X0 : G, (M.op (M.op x X0) x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14373 eq14371
    | exact resolve eq14371 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14371
  have eq14569 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq14373 eq14474
    | exact resolve eq14474 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14474
  have eq14576 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14373 eq14483
    | exact resolve eq14483 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14483
  have eq14579 : (σ x) = (σ (σ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14373 eq14487
    | exact resolve eq14487 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14487
  have eq14583 : (σ (σ x)) = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14373 eq14494
    | exact resolve eq14494 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14494
  have eq14593 : (σ x) = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14373 eq14511
    | exact resolve eq14511 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14511
  have eq14620 : x = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14373 eq14576
    | exact resolve eq14576 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14576
  have eq14622 : (σ x) = (σ (σ (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14579
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14579
    | exact resolve eq14579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14579
  have eq14639 : (σ x) = (σ (τ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14583 eq14622
    | exact resolve eq14622 eq14583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14583 eq14622
  have eq14647 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14639
       have i₂ := eq14 x
       grind)
    | exact superpose eq14 eq14639
    | exact resolve eq14639 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14639
  have eq14663 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq14647 eq31
    | exact resolve eq31 eq14647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14689 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq14663
    | exact resolve eq14663 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14663
  have eq14690 : x = (σ x) ∨ x = y := by grind
  clear eq14689
  have eq14692 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq14690
       grind)
    | exact superpose eq14690 eq18
    | exact resolve eq18 eq14690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14693 : (σ x) = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq14690
       grind)
    | exact superpose eq14690 eq22
    | exact resolve eq22 eq14690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14694 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (σ x) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq14690
       grind)
    | exact superpose eq14690 eq35
    | exact resolve eq35 eq14690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq15519 : ∀ X0 X1 : G, (M.op (τ (k X0 X0)) (M.op X1 (σ x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1102 X0 x X1
       have i₂ := eq14535 x
       grind)
    | exact superpose eq14535 eq1102
    | exact resolve eq1102 eq14535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq15743 : ∀ X1 : G, (M.op (τ x) (M.op X1 (σ x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq14373 eq15519
    | exact resolve eq15519 eq14373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14373 eq15519
  have eq15927 : ∀ X1 : G, (M.op (σ x) (M.op X1 (σ x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq14593 eq15743
    | exact resolve eq15743 eq14593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14593 eq15743
  have eq17228 : (k (σ x) (σ (σ y))) = (σ (σ (M.op x y))) ∨ x = y ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq4235 eq14694
    | exact resolve eq14694 eq4235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4235
  have eq17300 : (k (σ x) (σ (σ y))) = (σ (σ (M.op x y))) ∨ x = y ∨ x = (k x x) := by grind
  clear eq17228
  have eq17366 : (k (σ x) (σ (σ y))) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14690 eq17300
    | exact resolve eq17300 eq14690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17300
  have eq17380 : (k (σ x) (σ (σ x))) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14535 eq17366
    | (have j1 := eq14535 (σ x)
       grind)
    | exact resolve eq17366 eq14535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17366
  have eq17384 : (k (σ x) (σ x)) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14693 eq17380
    | exact resolve eq17380 eq14693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17380
  have eq17579 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14538 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14538
    | (have j0 := eq14538 y
       grind)
    | exact resolve eq14538 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14538
  have eq17627 : y = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14647 eq17579
    | exact resolve eq17579 eq14647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17579
  have eq17857 : ∀ X0 : G, x ≠ (M.op (σ x) x) ∨ x = X0 ∨ (k x X0) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq14569 x
       grind)
    | exact superpose eq14569 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq14569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14569
  have eq17931 : ∀ X0 : G, x = X0 ∨ (k x X0) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq17857 X0
       grind)
    | (have r₁ := eq17857 X0
       have r₂ := eq14620
       grind)
    | exact resolve eq17857 eq14620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14620 eq17857
  have eq17965 : ∀ X0 : G, (σ x) = X0 ∨ (k x X0) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14647 eq17931
    | (have j0 := eq17931 y
       grind)
    | exact resolve eq17931 eq14647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17931
  have eq17988 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14647 eq17965
    | (have j0 := eq17965 X0
       grind)
    | exact resolve eq17965 eq14647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14647 eq17965
  have eq23236 : ∀ X0 : G, (k X0 X0) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq17384 eq806
    | exact resolve eq806 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23240 : ∀ X0 : G, (k X0 X0) = (τ (σ (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq17384 eq847
    | exact resolve eq847 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq23273 : ∀ X0 : G, (k X0 X0) = (τ (τ (σ (σ (M.op x y))))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq17384 eq1348
    | exact resolve eq1348 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq23291 : ∀ X0 : G, (τ (k X0 X0)) = (τ (τ (σ (σ (M.op x y))))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq17384 eq1699
    | exact resolve eq1699 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699 eq17384
  have eq23391 : ∀ X0 : G, (τ (σ (M.op x y))) = (τ (k X0 X0)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq23291 X0
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq23291
    | exact resolve eq23291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23291
  have eq23397 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 X0) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq23273 X0
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq23273
    | exact resolve eq23273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23273
  have eq23423 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23240 X0
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq23240
    | exact resolve eq23240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23240
  have eq23483 : ∀ X0 : G, (M.op x y) = (τ (k X0 X0)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq28 eq23391
    | exact resolve eq23391 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23391
  have eq23484 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq28 eq23397
    | exact resolve eq23397 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23397
  have eq23530 : (M.op x y) = (τ (σ (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq23236 eq23483
    | exact resolve eq23483 eq23236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23236 eq23483
  have eq23552 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq23530
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq23530
    | exact resolve eq23530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23530
  have eq23631 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq23552 eq806
    | exact resolve eq806 eq23552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23552
  have eq26753 : ∀ X0 X1 : G, (σ x) = (k X0 X0) ∨ x = y ∨ (σ (M.op x y)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X0
       have i₂ := eq23423 X0
       grind)
    | exact superpose eq23423 eq806
    | (have j1 := eq23423 X1
       grind)
    | exact resolve eq806 eq23423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq23423
  have eq26984 : ∀ X0 X1 : G, (σ x) = (k X0 X0) ∨ x = y ∨ (M.op x y) = (k X1 X1) := by
    intro X0 X1
    first
    | exact superpose eq23631 eq26753
    | (have j0 := eq26753 X0 X1
       have j1 := eq23631 X0
       grind)
    | exact resolve eq26753 eq23631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631 eq26753
  have eq27292 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) (k X1 X1)) = X0 ∨ x = y ∨ (M.op x y) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq773 X0 X0 X2
       have i₂ := eq23484 X0
       grind)
    | exact superpose eq23484 eq773
    | (have j1 := eq23484 X2
       grind)
    | exact resolve eq773 eq23484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23484
  have eq27500 : ∀ X0 X2 : G, (M.op (M.op (σ x) X0) (σ x)) = X0 ∨ x = y ∨ (M.op x y) = (k X2 X2) := by
    intro X0 X2
    first
    | exact superpose eq26984 eq27292
    | (have j0 := eq27292 X0 x X2
       have j1 := eq26984 X0 X2
       grind)
    | exact resolve eq27292 eq26984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27292
  have eq29804 : ∀ X0 : G, (M.op x y) ≠ (σ x) ∨ x = y ∨ (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26984 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26984
  have eq53915 : ∀ X0 : G, y = (M.op (M.op x y) (σ x)) ∨ x = y ∨ (M.op x y) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14692 eq27500
    | (have j0 := eq27500 X0 X0
       grind)
    | exact resolve eq27500 eq14692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14692 eq27500
  have eq53973 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ x = y ∨ y = (M.op (M.op x y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq53915 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53915
  have eq54163 : x = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ x = y ∨ y = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq53973 x
       grind)
    | exact superpose eq53973 eq182
    | exact resolve eq182 eq53973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq54210 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) X1) (k X2 X2)) = X1 ∨ x = y ∨ y = (M.op (M.op x y) (σ x)) := by
    intro X1 X2
    first
    | (have i₁ := eq773 X2 x X1
       have i₂ := eq53973 x
       grind)
    | exact superpose eq53973 eq773
    | exact resolve eq773 eq53973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq54708 : ∀ X1 : G, (M.op (M.op (M.op x y) X1) (M.op x y)) = X1 ∨ x = y ∨ y = (M.op (M.op x y) (σ x)) := by
    intro X1
    first
    | exact superpose eq53973 eq54210
    | exact resolve eq54210 eq53973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53973 eq54210
  have eq54750 : (σ x) = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ x = y ∨ y = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq14690 eq54163
    | exact resolve eq54163 eq14690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14690 eq54163
  have eq65161 : y = (σ x) ∨ x = y ∨ y = (M.op (M.op x y) (σ x)) ∨ x = y ∨ y = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54750 eq54708
    | exact resolve eq54708 eq54750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54708 eq54750
  have eq65180 : y = (M.op (M.op x y) (σ x)) ∨ x = y ∨ y = (σ x) := by grind
  clear eq65161
  have eq103646 : ∀ X0 : G, (M.op (σ x) (k (σ x) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17988 eq15927
    | (have j1 := eq17988 (σ y)
       grind)
    | exact resolve eq15927 eq17988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15927
  have eq103745 : y = (k (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17988 eq17627
    | (have j1 := eq17988 (σ y)
       grind)
    | exact resolve eq17627 eq17988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17627 eq17988
  have eq103782 : y = (k (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ x) := by grind
  clear eq103745
  have eq103849 : ∀ X0 : G, (M.op (σ x) (k (σ x) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = X0 := by
    intro X0
    first
    | (have j0 := eq103646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103646
  have eq104183 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq103782 eq14694
    | exact resolve eq14694 eq103782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14694 eq103782
  have eq104186 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq104183
  have eq104189 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq20 eq104186
    | exact resolve eq104186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104186
  have eq104191 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq104189
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq104189
    | exact resolve eq104189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104189
  have eq104252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq104191 eq103849
    | (have j0 := eq103849 (σ y)
       grind)
    | exact resolve eq103849 eq104191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103849
  have eq104292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ x) := by grind
  clear eq104252
  have eq104315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq26 eq104292
    | exact resolve eq104292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104292
  have eq104325 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq104315
       have r₂ := eq27
       grind)
    | exact resolve eq104315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104315
  have eq104343 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq104325 eq31
    | exact resolve eq31 eq104325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104325
  have eq104392 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq29 eq104343
    | exact resolve eq104343 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104343
  have eq104393 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (M.op x y) = (σ x) := by grind
  clear eq104392
  have eq104434 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) ∨ x = y ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq104393 eq104191
    | exact resolve eq104191 eq104393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104191 eq104393
  have eq104435 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq104434
  have eq104448 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq14535 eq104435
    | exact resolve eq104435 eq14535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14535 eq104435
  have eq104449 : (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ x) := by grind
  clear eq104448
  have eq104481 : y = (τ (σ x)) ∨ x = y ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq104449 eq31
    | exact resolve eq31 eq104449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq104449
  have eq104534 : x = y ∨ x = y ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq29 eq104481
    | exact resolve eq104481 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq104481
  have eq104535 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq104534
  have eq104598 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq104535 eq14693
    | exact resolve eq14693 eq104535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14693
  have eq104644 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq104535 eq29804
    | (have j0 := eq29804 X0
       grind)
    | (have r₁ := eq29804 X0
       have r₂ := eq104535
       grind)
    | exact resolve eq29804 eq104535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29804
  have eq104686 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq104535 eq65180
    | exact resolve eq65180 eq104535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65180
  have eq104725 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq104686
  have eq104767 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104644
  have eq104768 : ∀ X0 : G, x = y ∨ (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104767 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104767
  have eq104815 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq104598
  have eq104842 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104725
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq104725
    | exact resolve eq104725 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104725
  have eq104871 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq104815
    | exact resolve eq104815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104815
  have eq104908 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq104768 eq104842
    | exact resolve eq104842 eq104768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104842
  have eq104909 : y = (M.op x y) ∨ x = y := by grind
  clear eq104908
  have eq105090 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq104909
       grind)
    | exact superpose eq104909 eq24
    | exact resolve eq24 eq104909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104909
  have eq105173 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq105090
    | exact resolve eq105090 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105090
  have eq105202 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq104871 eq105173
    | exact resolve eq105173 eq104871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105173
  have eq105310 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq105202 eq26
    | exact resolve eq26 eq105202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105202
  have eq105393 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq104535 eq105310
    | exact resolve eq105310 eq104535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104535 eq105310
  have eq105408 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq105393
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq105393
    | exact resolve eq105393 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105393
  have eq105420 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq104768 eq105408
    | exact resolve eq105408 eq104768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104768 eq105408
  have eq105459 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq105420 eq27
    | exact resolve eq27 eq105420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105420
  have eq105568 : x = y := by
    first
    | (have r₁ := eq105459
       have r₂ := eq104871
       grind)
    | exact resolve eq105459 eq104871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104871 eq105459
  have eq105591 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq105568
       grind)
    | exact superpose eq105568 eq18
    | exact resolve eq18 eq105568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq105592 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq105568
       grind)
    | exact superpose eq105568 eq24
    | exact resolve eq24 eq105568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq105568
  have eq105608 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq105592
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105592
    | exact resolve eq105592 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105592
  have eq105609 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq105591
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq105591
    | exact resolve eq105591 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105591
  have eq105611 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105608 eq26
    | exact resolve eq26 eq105608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq105608
  have eq105653 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq105611
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq105611
    | exact resolve eq105611 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq105611
  have eq105674 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq105609
       grind)
    | exact superpose eq105609 eq39
    | exact resolve eq39 eq105609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq105609
  have eq106022 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq105674
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105674
    | exact resolve eq105674 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq105674
  have eq106082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105653 eq106022
    | exact resolve eq106022 eq105653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105653 eq106022
  have eq106124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq106082
    | exact resolve eq106082 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq106082
  have eq106156 : False := by grind
  exact eq106156

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq30 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq43 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq54 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq78 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y X0
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq78 eq54
    | exact resolve eq54 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  clear eq19
  have eq100 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ y) (σ (k y x))
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq135 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq131
    | exact resolve eq131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq15
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq138
    | exact resolve eq138 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq10
    | exact resolve eq10 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq29
    | exact resolve eq29 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq222 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq37
    | exact resolve eq37 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq260 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq214 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1477 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq217 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq217
    | (have j0 := eq217 x
       grind)
    | exact resolve eq217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1508 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1477 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq14 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1509 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq54 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1508
       have i₂ := eq54 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq54 eq1508
    | exact resolve eq1508 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508
  have eq2244 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq222
    | (have j0 := eq222 (M.op x y)
       grind)
    | exact resolve eq222 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2296 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2244 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2297 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2296
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2296
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq2296
    | exact resolve eq2296 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq5428 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0 X1
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq95
    | (have j0 := eq95 X0 X0 X1
       grind)
    | (have r₁ := eq95 x x x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq95 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5429 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq5433 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq84 eq100
    | (have r₁ := eq100 (M.op x y) y
       have r₂ := eq84 (M.op x y)
       grind)
    | exact resolve eq100 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5434 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq81 eq100
    | (have r₁ := eq100 x (M.op x y)
       have r₂ := eq81 x
       grind)
    | exact resolve eq100 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq5440 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5434
  have eq5441 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5433
  have eq5445 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5440 eq1509
    | exact resolve eq1509 eq5440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq5440
  have eq5448 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5441 eq2297
    | exact resolve eq2297 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq5449 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5441 eq2244
    | exact resolve eq2244 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq5441
  have eq5451 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5445
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5445
    | exact resolve eq5445 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq5453 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq5449
    | exact resolve eq5449 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5454 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq5448
    | exact resolve eq5448 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448
  have eq11122 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq5451 eq54
    | exact resolve eq54 eq5451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5451
  have eq11135 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5454 eq54
    | exact resolve eq54 eq5454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11135 eq11122
    | exact resolve eq11122 eq11135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11135
  have eq12211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq12195
    | exact resolve eq12195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195
  have eq12213 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12211
       have r₂ := eq28
       grind)
    | exact resolve eq12211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211
  have eq12248 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12213 eq5429
    | exact resolve eq5429 eq12213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12213
  have eq12255 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12248
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq12248
    | exact resolve eq12248 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12248
  have eq12932 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12255 eq260
    | exact resolve eq260 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq12950 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12255
  have eq12960 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq38 eq12932
    | exact resolve eq12932 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12932
  have eq12975 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq40 eq12960
    | exact resolve eq12960 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12960
  have eq13105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12975 eq5454
    | exact resolve eq5454 eq12975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5454 eq12975
  have eq13137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13105
  have eq13149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq13137
    | exact resolve eq13137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13137
  have eq13161 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13149
       have r₂ := eq28
       grind)
    | exact resolve eq13149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13149
  have eq13170 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13161 eq139
    | exact resolve eq139 eq13161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13161
  have eq13198 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq13170
    | exact resolve eq13170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13170
  have eq13201 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13198
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13198
    | exact resolve eq13198 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13198
  have eq13250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13201 eq11122
    | exact resolve eq11122 eq13201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13250
  have eq13291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq13277
    | exact resolve eq13277 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13277
  have eq13303 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13291
       have r₂ := eq28
       grind)
    | exact resolve eq13291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13291
  have eq13396 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13303 eq5429
    | exact resolve eq5429 eq13303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13303
  have eq13403 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13396
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq13396
    | exact resolve eq13396 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13396
  have eq13420 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13403
       have r₂ := eq12950
       grind)
    | exact resolve eq13403 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12950 eq13403
  have eq13438 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13420 eq13201
    | exact resolve eq13201 eq13420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13439 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13420 eq11122
    | exact resolve eq11122 eq13420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13420
  have eq13466 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13439
  have eq13467 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13438
  have eq13493 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13467 eq27
    | exact resolve eq27 eq13467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13497 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13467 eq40
    | exact resolve eq40 eq13467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13467
  have eq13553 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq39 eq13497
    | exact resolve eq13497 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13497
  have eq13562 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq13553 eq40
    | exact resolve eq40 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13553
  have eq13609 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq13562
    | exact resolve eq13562 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562
  have eq13617 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13609 eq39
    | exact resolve eq39 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13609
  have eq13665 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq13617
    | exact resolve eq13617 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13617
  have eq14526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13493 eq13466
    | exact resolve eq13466 eq13493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13466 eq13493
  have eq14556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14526
  have eq14573 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq14556
       have r₂ := eq28
       grind)
    | exact resolve eq14556 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14556
  have eq14584 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14573 eq40
    | exact resolve eq40 eq14573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq14573
  have eq14631 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq14584
    | exact resolve eq14584 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14584
  have eq14639 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14631 eq39
    | exact resolve eq39 eq14631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14631
  have eq14687 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq14639
    | exact resolve eq14639 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14639
  have eq14691 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14687 eq21
    | exact resolve eq21 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14692 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14687 eq78
    | exact resolve eq78 eq14687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq14718 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq14687
  have eq14719 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14691
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14691
    | exact resolve eq14691 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14691
  have eq16166 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14692 (M.op y x)
       have i₂ := eq14692 x
       grind)
    | exact superpose eq14692 eq14692
    | exact resolve eq14692 eq14692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14692
  have eq16180 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq16166
  have eq16201 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139 y
       have i₂ := eq16180
       grind)
    | exact superpose eq16180 eq139
    | exact resolve eq139 eq16180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16180
  have eq16229 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16201
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16201
    | exact resolve eq16201 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16201
  have eq16232 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14719 eq16229
    | exact resolve eq16229 eq14719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14719 eq16229
  have eq16283 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16232
  have eq16338 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16283 eq5453
    | exact resolve eq5453 eq16283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5453
  have eq16397 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43 eq16338
    | exact resolve eq16338 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq16338
  have eq16884 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13665 eq16397
    | exact resolve eq16397 eq13665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13665 eq16397
  have eq16932 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq16884
  have eq16965 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16932
       have r₂ := eq14718
       grind)
    | exact resolve eq16932 eq14718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14718 eq16932
  have eq16968 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16965
       have i₂ := eq101 y
       grind)
    | exact superpose eq101 eq16965
    | exact resolve eq16965 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16965
  have eq16970 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16968
       have i₂ := eq139 y
       grind)
    | exact superpose eq139 eq16968
    | exact resolve eq16968 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968
  have eq16972 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16970
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16970
    | exact resolve eq16970 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16970
  have eq17013 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16972 eq5429
    | exact resolve eq5429 eq16972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16972
  have eq17024 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17013
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq17013
    | exact resolve eq17013 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17013
  have eq17077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17024 eq11122
    | exact resolve eq11122 eq17024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11122 eq17024
  have eq17117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17077
    | exact resolve eq17077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17077
  have eq17129 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17117
       have r₂ := eq28
       grind)
    | exact resolve eq17117 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17117
  have eq35299 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17129 eq5429
    | exact resolve eq5429 eq17129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429 eq17129
  have eq35308 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35299
       have i₂ := eq101 sF1
       grind)
    | exact superpose eq101 eq35299
    | exact resolve eq35299 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq35299
  have eq37124 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35308 eq16283
    | exact resolve eq16283 eq35308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16283 eq35308
  have eq37190 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq37124
  have eq37221 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37190 eq39
    | exact resolve eq39 eq37190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq37190
  have eq37275 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq37221
    | exact resolve eq37221 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq37221
  have eq37276 : x = (M.op x y) := by grind
  clear eq37275
  have eq37281 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37276 eq21
    | exact resolve eq21 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq37290 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq37276 eq81
    | exact resolve eq81 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq37293 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq37276 eq96
    | exact resolve eq96 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq40764 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq37276 eq37293
    | exact resolve eq37293 eq37276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37276 eq37293
  have eq40767 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37281
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37281
    | exact resolve eq37281 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37281
  have eq41109 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40767 eq23
    | exact resolve eq23 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq41110 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40767 eq27
    | exact resolve eq27 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41122 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40767 eq135
    | exact resolve eq135 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq43088 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq40767 eq41122
    | exact resolve eq41122 eq40767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40767 eq41122
  have eq43635 : x = (M.op x x) := by
    first
    | (have i₁ := eq37290 (M.op x x)
       have i₂ := eq37290 x
       grind)
    | exact superpose eq37290 eq37290
    | exact resolve eq37290 eq37290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37290
  have eq43783 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq40764
       have i₂ := eq43635
       grind)
    | exact superpose eq43635 eq40764
    | (have r₁ := eq40764
       have r₂ := eq43635
       grind)
    | exact resolve eq40764 eq43635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40764
  have eq43805 : x = (k y x) := by grind
  clear eq43783
  have eq43849 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43088
       have i₂ := eq43805
       grind)
    | exact superpose eq43805 eq43088
    | exact resolve eq43088 eq43805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43088 eq43805
  have eq43874 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq43849
       have i₂ := eq41109
       grind)
    | exact superpose eq41109 eq43849
    | exact resolve eq43849 eq41109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43849
  have eq43875 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq43874
  have eq44056 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq139 x
       have i₂ := eq43635
       grind)
    | exact superpose eq43635 eq139
    | exact resolve eq139 eq43635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq43635
  have eq44110 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44056
       have i₂ := eq41109
       grind)
    | exact superpose eq41109 eq44056
    | exact resolve eq44056 eq41109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41109 eq44056
  have eq44283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44110 eq43875
    | exact resolve eq43875 eq44110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43875
  have eq44297 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq44283
       have r₂ := eq28
       grind)
    | exact resolve eq44283 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44283
  have eq45356 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44297 eq41110
    | exact resolve eq41110 eq44297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41110 eq44297
  have eq45398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44110 eq45356
    | exact resolve eq45356 eq44110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44110 eq45356
  have eq45873 : False := by grind
  exact eq45873

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  clear eq25 eq36
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq116 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ X0 ∨ (M.op (M.op X1 X2) X0) = (M.op (M.op X0 X3) (M.op X0 X3)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X0 X3)) = (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) X0) (M.op X0 X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 X2) X0) (M.op X0 X3)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq211 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
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
  have eq212 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq220 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq211 eq14
    | exact resolve eq14 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq346 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq372 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq674 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) ∨ (M.op x x) = (k x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq211 eq117
    | exact resolve eq117 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq687 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq346 X0 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq346
    | exact resolve eq346 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq346 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq346
    | (have j0 := eq346 X0 x
       grind)
    | exact resolve eq346 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : (k (k x x) x) = (τ (k (k (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq50 eq696
    | exact resolve eq696 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 : G, (k (k x x) (τ X0)) = (τ (k (k (σ x) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq372 (k x x) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq372
    | exact resolve eq372 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq762 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq372 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq372
    | (have j0 := eq372 x X0
       grind)
    | exact resolve eq372 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4180 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq10805 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10805
    | exact resolve eq10805 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10805
  have eq10824 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10813
       have r₂ := eq28
       grind)
    | exact resolve eq10813 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10813
  have eq10826 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10824
    | exact resolve eq10824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10824
  have eq10830 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq10826
  have eq10846 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10830
    | exact resolve eq10830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10830
  have eq10874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10846 eq95
    | exact resolve eq95 eq10846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq10846
  have eq10889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10874
  have eq10891 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10889
       have r₂ := eq28
       grind)
    | exact resolve eq10889 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10889
  have eq10895 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10891
  have eq10911 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10895
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10895
    | exact resolve eq10895 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10895
  have eq10935 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10911
       grind)
    | exact superpose eq10911 eq45
    | exact resolve eq45 eq10911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10911
  have eq10963 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10935
    | exact resolve eq10935 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10935
  have eq11040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10963 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq10963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11040
    | exact resolve eq11040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11040
  have eq11061 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11050
       have r₂ := eq28
       grind)
    | exact resolve eq11050 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11050
  have eq11063 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11061
    | exact resolve eq11061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11061
  have eq11064 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11063
  have eq11069 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11064
  have eq11085 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11069
    | exact resolve eq11069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq11344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11085 eq10963
    | exact resolve eq10963 eq11085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10963 eq11085
  have eq11353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11344
  have eq11357 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11353
       have r₂ := eq28
       grind)
    | exact resolve eq11353 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11353
  have eq11361 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11357 eq116
    | (have r₁ := eq116
       have r₂ := eq11357
       grind)
    | exact resolve eq116 eq11357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq11362 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11357 eq212
    | exact resolve eq212 eq11357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq11371 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11357 eq256
    | exact resolve eq256 eq11357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq11378 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11361
  have eq11611 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11362 eq266
    | exact resolve eq266 eq11362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq11362
  have eq11629 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11357 eq11611
    | exact resolve eq11611 eq11357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11357 eq11611
  have eq11648 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11629
  have eq11875 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11648 eq281
    | exact resolve eq281 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12809 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11875 eq50
    | exact resolve eq50 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13110 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11648 eq12809
    | exact resolve eq12809 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12809
  have eq13137 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq13110
  have eq13141 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq13137
    | exact resolve eq13137 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13137
  have eq13155 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq13141
       grind)
    | exact superpose eq13141 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq13141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13172 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq13155
  have eq13196 : (k x x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281 x
       have i₂ := eq13172
       grind)
    | exact superpose eq13172 eq281
    | exact resolve eq281 eq13172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13203 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 x x X0
       have i₂ := eq13172
       grind)
    | exact superpose eq13172 eq53
    | exact resolve eq53 eq13172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq13172
  have eq15004 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (k (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq687 X0
       have i₂ := eq13141
       grind)
    | exact superpose eq13141 eq687
    | exact resolve eq687 eq13141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq15038 : ∀ X0 : G, (τ (k X0 (k (σ x) (σ x)))) = (τ (k X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15004 X0
       have i₂ := eq696 X0
       grind)
    | exact superpose eq696 eq15004
    | exact resolve eq15004 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq15004
  have eq16438 : ∀ X0 : G, (k x (τ X0)) = (τ (k (k (σ x) (σ x)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq13141
       grind)
    | exact superpose eq13141 eq753
    | exact resolve eq753 eq13141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq13141
  have eq16543 : ∀ X0 : G, (τ (k (k (σ x) (σ x)) X0)) = (τ (k (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16438 X0
       have i₂ := eq762 X0
       grind)
    | exact superpose eq762 eq16438
    | exact resolve eq16438 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq16438
  have eq18256 : ∀ X0 : G, (k X0 (τ (k (σ x) (σ x)))) = (τ (k (σ X0) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15038 eq372
    | exact resolve eq372 eq15038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18260 : ∀ X0 : G, (k X0 (k (σ x) (σ x))) = (σ (τ (k X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15038 eq15
    | exact resolve eq15 eq15038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15038
  have eq18347 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18260 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq18260
    | exact resolve eq18260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18260
  have eq18351 : ∀ X0 : G, (k X0 (τ (k (σ x) (σ x)))) = (k X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18256 X0
       have i₂ := eq372 X0 sF2
       grind)
    | exact superpose eq372 eq18256
    | exact resolve eq18256 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq18256
  have eq18357 : ∀ X0 : G, (k X0 x) = (k X0 (τ (k (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq18351
    | exact resolve eq18351 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18351
  have eq18360 : ∀ X0 : G, (k X0 x) = (k X0 (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50 eq18357
    | exact resolve eq18357 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18357
  have eq18363 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11875 eq18347
    | exact resolve eq18347 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18347
  have eq18398 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18363
  have eq18429 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18360 X0
       have i₂ := eq13196
       grind)
    | exact superpose eq13196 eq18360
    | exact resolve eq18360 eq13196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13196 eq18360
  have eq18464 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18429
  have eq18525 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18398 sF2
       have i₂ := eq281 sF2
       grind)
    | exact superpose eq281 eq18398
    | exact resolve eq18398 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22326 : ∀ X0 : G, (k (τ (k (σ x) (σ x))) X0) = (τ (k (σ x) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16543 eq346
    | exact resolve eq346 eq16543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22328 : ∀ X0 : G, (k (k (σ x) (σ x)) X0) = (σ (τ (k (σ x) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16543 eq15
    | exact resolve eq15 eq16543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16543
  have eq22423 : ∀ X0 : G, (k (σ x) X0) = (k (k (σ x) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22328 X0
       have i₂ := eq15 (k sF2 X0)
       grind)
    | exact superpose eq15 eq22328
    | exact resolve eq22328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22328
  have eq22425 : ∀ X0 : G, (k (τ (k (σ x) (σ x))) X0) = (k (τ (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22326 x
       have i₂ := eq346 sF2 x
       grind)
    | exact superpose eq346 eq22326
    | exact resolve eq22326 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq22326
  have eq22439 : ∀ X0 : G, (k x X0) = (k (τ (k (σ x) (σ x))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq22425
    | exact resolve eq22425 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22425
  have eq22446 : ∀ X0 : G, (k x X0) = (k (k x x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50 eq22439
    | exact resolve eq22439 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq22439
  have eq22451 : ∀ X0 : G, (k (σ x) X0) = (k (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11875 eq22423
    | exact resolve eq22423 eq11875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875 eq22423
  have eq22518 : ∀ X0 : G, (k (σ x) X0) = (k (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22451
  have eq22600 : (k (k x x) x) = (k x (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18464 (k x x)
       have i₂ := eq22446 (M.op x x)
       grind)
    | exact superpose eq22446 eq18464
    | exact resolve eq18464 eq22446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18464 eq22446
  have eq22633 : (k (k x x) x) = (k x (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq22600
  have eq22664 : (k (k x x) x) = (M.op x (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22633
       have i₂ := eq281 x
       grind)
    | exact superpose eq281 eq22633
    | exact resolve eq22633 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22633
  have eq22762 : (k (σ x) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22518 eq18398
    | exact resolve eq18398 eq22518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18398 eq22518
  have eq22793 : (k (σ x) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22762
  have eq22821 : (k (σ x) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22793
  have eq22845 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22821
       have i₂ := eq281 sF2
       grind)
    | exact superpose eq281 eq22821
    | exact resolve eq22821 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22821
  have eq29218 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22845 eq14
    | exact resolve eq14 eq22845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22845
  have eq43924 : (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) = (k (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29218 eq281
    | exact resolve eq281 eq29218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq29218
  have eq43960 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43924
       have i₂ := eq267 sF2 sF2 sF2
       grind)
    | exact superpose eq267 eq43924
    | exact resolve eq43924 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq43924
  have eq66706 : (M.op (σ x) (σ x)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18525 eq43960
    | exact resolve eq43960 eq18525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18525 eq43960
  have eq66720 : (M.op (σ x) (σ x)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq66706
  have eq66740 : (τ (M.op (σ x) (σ x))) = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66720 eq717
    | exact resolve eq717 eq66720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq66720
  have eq67223 : (τ (M.op (σ x) (σ x))) = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22664
       have i₂ := eq66740
       grind)
    | exact superpose eq66740 eq22664
    | exact resolve eq22664 eq66740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22664 eq66740
  have eq67243 : (τ (M.op (σ x) (σ x))) = (M.op x (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq67223
  have eq68271 : x = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13203 (M.op x x)
       have i₂ := eq67243
       grind)
    | exact superpose eq67243 eq13203
    | exact resolve eq13203 eq67243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13203 eq67243
  have eq68290 : x = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq68271
  have eq88608 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11378 eq61
    | exact resolve eq61 eq11378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq11378
  have eq153961 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11648 eq88608
    | exact resolve eq88608 eq11648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11648 eq88608
  have eq154255 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq153961
  have eq154263 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq154255
    | exact resolve eq154255 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq154255
  have eq154265 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq154263 eq11371
    | exact resolve eq11371 eq154263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11371 eq154263
  have eq154287 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq154265
  have eq154436 : x = (M.op x (τ (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq154287 eq68290
    | exact resolve eq68290 eq154287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68290 eq154287
  have eq154564 : x = (M.op x (τ (σ y))) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq154436
  have eq154680 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq30 eq154564
    | exact resolve eq154564 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq154564
  have eq154729 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq154680
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq154680
    | exact resolve eq154680 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154680
  have eq154730 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq154729
  have eq154749 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq154730
       grind)
    | exact superpose eq154730 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq154730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154760 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq154749
  have eq154772 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154760
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq154760
    | exact resolve eq154760 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154760
  have eq154773 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq154772
  have eq154832 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq154773
  have eq154850 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154832
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq154832
    | exact resolve eq154832 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq154832
  have eq155019 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154730
       have i₂ := eq154850
       grind)
    | exact superpose eq154850 eq154730
    | exact resolve eq154730 eq154850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154730 eq154850
  have eq155031 : x = (M.op x y) := by grind
  clear eq155019
  have eq155076 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq155031 eq21
    | exact resolve eq21 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq155127 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq155031 eq211
    | exact resolve eq211 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq155132 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq155031 eq220
    | exact resolve eq220 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq155136 : ∀ X0 : G, y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq155031 eq255
    | exact resolve eq255 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq155369 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq155076
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq155076
    | exact resolve eq155076 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155076
  have eq155396 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq155369 eq27
    | exact resolve eq27 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155897 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq265 (M.op x x)
       have i₂ := eq155127
       grind)
    | exact superpose eq155127 eq265
    | exact resolve eq265 eq155127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq155127
  have eq155916 : x = (M.op x x) := by
    first
    | exact superpose eq155031 eq155897
    | exact resolve eq155897 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155897
  have eq164389 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) ∨ (M.op x x) = (k x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq674 X0
       grind)
    | (have r₁ := eq674 X0
       have r₂ := eq155031
       grind)
    | exact resolve eq674 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq164390 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x X0)) ∨ (M.op x x) = (k x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq155031 eq164389
    | (have j0 := eq164389 X0
       grind)
    | exact resolve eq164389 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164389
  have eq164391 : ∀ X0 : G, (M.op x x) = (k x (M.op x X0)) ∨ x = (M.op (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq155031 eq164390
    | (have j0 := eq164390 X0
       grind)
    | exact resolve eq164390 eq155031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155031 eq164390
  have eq164392 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x X0)) ∨ x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq164391 X0
       have i₂ := eq155916
       grind)
    | exact superpose eq155916 eq164391
    | (have j0 := eq164391 X0
       grind)
    | exact resolve eq164391 eq155916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155916 eq164391
  have eq164426 : ∀ X0 : G, (M.op x (M.op x X0)) = (k x (M.op x X0)) ∨ x = (k x (M.op x X0)) := by
    intro X0
    grind
  clear eq164392
  have eq164445 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq164426 X0
       have i₂ := eq155132 X0
       grind)
    | exact superpose eq155132 eq164426
    | (have j0 := eq164426 X0
       grind)
    | exact resolve eq164426 eq155132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155132 eq164426
  have eq164446 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq164445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164445
  have eq164457 : x = (k x y) := by
    first
    | (have i₁ := eq164446 (M.op y x)
       have i₂ := eq155136 x
       grind)
    | exact superpose eq155136 eq164446
    | exact resolve eq164446 eq155136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155136 eq164446
  have eq164530 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq164457
       grind)
    | exact superpose eq164457 eq45
    | exact resolve eq45 eq164457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq164546 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4180 x
       have i₂ := eq164457
       grind)
    | exact superpose eq164457 eq4180
    | (have j0 := eq4180 x
       grind)
    | exact resolve eq4180 eq164457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4180 eq164457
  have eq164561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq164546
  have eq164578 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq164561
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164561
    | exact resolve eq164561 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164561
  have eq164591 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq155369 eq164530
    | exact resolve eq164530 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164530
  have eq164603 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq164578
    | exact resolve eq164578 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq164578
  have eq164616 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq164591
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164591
    | exact resolve eq164591 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164591
  have eq164622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq155369 eq164603
    | exact resolve eq164603 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164603
  have eq164634 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq155369 eq164616
    | exact resolve eq164616 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164616
  have eq164638 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq164622
       have r₂ := eq28
       grind)
    | exact resolve eq164622 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164622
  have eq164645 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq164638
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164638
    | exact resolve eq164638 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq164638
  have eq164649 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq155369 eq164645
    | exact resolve eq164645 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155369 eq164645
  have eq164749 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq164649
  have eq164769 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq155396 eq164749
    | exact resolve eq164749 eq155396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155396 eq164749
  have eq164770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq164634 eq164769
    | exact resolve eq164769 eq164634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164634 eq164769
  have eq164771 : False := by grind
  exact eq164771
