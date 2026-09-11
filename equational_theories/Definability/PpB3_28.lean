import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X0) X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq60 (M.op X0 X0) X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq210 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq216 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq130
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq225 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq216
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq216
    | exact resolve eq216 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq225
    | exact resolve eq225 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq344 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210
       have i₂ := eq86 X0 sF2
       grind)
    | (have i₁ := eq210
       have i₂ := eq86 sF2 x
       grind)
    | exact superpose eq86 eq210
    | exact resolve eq210 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq210
  have eq378 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq61
    | exact resolve eq61 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq61
  have eq10025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq226 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq10026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10025
    | exact resolve eq10025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10025
  have eq10037 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10026
       have r₂ := eq28
       grind)
    | exact resolve eq10026 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10026
  have eq10043 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10037 eq56
    | exact resolve eq56 eq10037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq10037
  have eq10048 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq10043
    | exact resolve eq10043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10043
  have eq10051 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq60 x y
       have i₂ := eq10048
       grind)
    | exact superpose eq10048 eq60
    | exact resolve eq60 eq10048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10048
  have eq10319 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq378 x X0
       have i₂ := eq10051
       grind)
    | exact superpose eq10051 eq378
    | exact resolve eq378 eq10051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq10051
  have eq10343 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10319 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10319
    | (have j0 := eq10319 X0
       grind)
    | exact resolve eq10319 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10319
  have eq11946 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq10343 eq67
    | exact resolve eq67 eq10343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq10343
  have eq11982 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11946
  have eq12012 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11982 eq28
    | exact resolve eq28 eq11982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12013 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11982 eq58
    | exact resolve eq58 eq11982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq11982
  have eq12163 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12013 eq344
    | exact resolve eq344 eq12013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12013
  have eq12195 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq12163
    | exact resolve eq12163 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12163
  have eq14027 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq60 x x
       have i₂ := eq12195
       grind)
    | exact superpose eq12195 eq60
    | exact resolve eq60 eq12195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq12195
  have eq14034 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14027
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14027
    | exact resolve eq14027 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14027
  have eq14061 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14034 eq30
    | exact resolve eq30 eq14034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14034
  have eq14195 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq14061
    | exact resolve eq14061 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14061
  have eq14196 : x = (M.op x y) ∨ x = y := by grind
  clear eq14195
  have eq14218 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14196 eq21
    | exact resolve eq21 eq14196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14327 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14218
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14218
    | exact resolve eq14218 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14218
  have eq14560 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14327 eq12012
    | (have r₁ := eq12012
       have r₂ := eq14327
       grind)
    | exact resolve eq12012 eq14327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12012 eq14327
  have eq14571 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq14560
  have eq14572 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq14571
  have eq14665 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14572 eq30
    | exact resolve eq30 eq14572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14572
  have eq14830 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq14665
    | exact resolve eq14665 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14665
  have eq15119 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14830 eq14196
    | exact resolve eq14196 eq14830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14196 eq14830
  have eq15120 : x = y := by grind
  clear eq15119
  have eq15212 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15120
       grind)
    | exact superpose eq15120 eq19
    | exact resolve eq19 eq15120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15213 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15120
       grind)
    | exact superpose eq15120 eq25
    | exact resolve eq25 eq15120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15120
  have eq15327 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15213
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15213
    | exact resolve eq15213 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15213
  have eq15360 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15327 eq27
    | exact resolve eq27 eq15327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15327
  have eq15889 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15360 eq344
    | exact resolve eq344 eq15360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq15360
  have eq15924 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15889
       have i₂ := eq15212
       grind)
    | exact superpose eq15212 eq15889
    | exact resolve eq15889 eq15212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15212 eq15889
  have eq16103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15924 eq15
    | exact resolve eq15 eq15924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15924
  have eq16158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16103
    | exact resolve eq16103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16103
  have eq16174 : False := by grind
  exact eq16174

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X2 X2) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X2 X2) (M.op X3 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X0)) X0) = X2 ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X2 : G, X0 = X2 ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq35 X0 x X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0 x X2
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq40 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have j0 := eq39 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq46 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X1 X0) X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (σ (M.op X0 X0)) (M.op X3 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X1 (σ X0) X3
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X2 X2)) X1 (M.op X2 X2) (M.op X3 X3)
       have i₂ := eq24 (M.op X2 X2) X2 X3 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq118 : ∀ X2 X3 : G, (M.op X2 X2) = (M.op X3 X3) := by
    intro X2 X3
    first
    | (have i₁ := eq103 x x X3 X2
       have i₂ := eq9 (M.op X3 X3) x x
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq123 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (σ (M.op X0 X0)) (M.op X3 X2))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq96 X0 x X2 X3
       have i₂ := eq51 x X2
       grind)
    | exact superpose eq51 eq96
    | exact resolve eq96 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq283 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq43
    | (have j0 := eq43 X0 X1
       have j1 := eq40 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq545 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (M.op X1 X1) X0
       have i₂ := eq51 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq51 eq46
    | exact resolve eq46 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq594 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq118 (σ X1) X0
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq118 X0 (σ X1)
       grind)
    | exact superpose eq118 eq22
    | exact resolve eq22 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118
  have eq1322 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X1 (σ (M.op X2 X2))
       have i₂ := eq123 X2 (M.op X1 X1) X0
       grind)
    | exact superpose eq123 eq9
    | exact resolve eq9 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1333 : ∀ X0 X2 : G, (M.op X0 (σ (M.op X2 X2))) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq1322 X0 x X2
       have i₂ := eq545 X0 x
       grind)
    | exact superpose eq545 eq1322
    | exact resolve eq1322 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq1322
  have eq3642 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq16
    | (have j1 := eq283 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq283 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq283 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq283 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq3688 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3642
  have eq5876 : (σ x) = (M.op (σ y) (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46 (σ y) (σ x)
       have i₂ := eq3688
       grind)
    | exact superpose eq3688 eq46
    | exact resolve eq46 eq3688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq3688
  have eq5915 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5876
       have i₂ := eq1333 (σ y) x
       grind)
    | exact superpose eq1333 eq5876
    | exact resolve eq5876 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333 eq5876
  have eq5916 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq5915
  have eq7098 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5916
       grind)
    | exact superpose eq5916 eq10
    | exact resolve eq10 eq5916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5916
  have eq7139 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7098
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7098
    | exact resolve eq7098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7098
  have eq7140 : x = y := by grind
  clear eq7139
  have eq9949 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7140
       grind)
    | exact superpose eq7140 eq16
    | exact resolve eq16 eq7140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7140
  have eq9950 : False := by grind
  exact eq9950

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X0) X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq60 (M.op X0 X0) X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq129 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq206 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52
       have i₂ := eq91 X0 x
       grind)
    | (have i₁ := eq52
       have i₂ := eq91 x X0
       grind)
    | exact superpose eq91 eq52
    | exact resolve eq52 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq216 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq129
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq225 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq216
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq216
    | exact resolve eq216 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq225
    | exact resolve eq225 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq226
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq226
    | exact resolve eq226 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq343 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210
       have i₂ := eq91 X0 sF2
       grind)
    | (have i₁ := eq210
       have i₂ := eq91 sF2 x
       grind)
    | exact superpose eq91 eq210
    | exact resolve eq210 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq210
  have eq378 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq61
    | exact resolve eq61 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq227 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq917
    | exact resolve eq917 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq921 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq918
       have r₂ := eq28
       grind)
    | exact resolve eq918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq923 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq921
    | exact resolve eq921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq925 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq923 eq73
    | (have r₁ := eq73
       have r₂ := eq923
       grind)
    | exact resolve eq73 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq927 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq923 eq58
    | exact resolve eq58 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq923
  have eq929 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq925
  have eq930 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq929
  have eq1052 : (σ y) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq927 eq206
    | exact resolve eq206 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq927
  have eq1066 : (σ y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1052 eq16
    | exact resolve eq16 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1081 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1066
    | exact resolve eq1066 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1085 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1081 eq30
    | exact resolve eq30 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1105 : x = y ∨ y = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1085
    | exact resolve eq1085 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1106 : y = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1105
  have eq1161 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1106 eq27
    | exact resolve eq27 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq930 eq227
    | exact resolve eq227 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq930
  have eq1330 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1326
  have eq1424 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1330 eq30
    | exact resolve eq30 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1447 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq1424
    | exact resolve eq1424 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1424
  have eq1448 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1447
  have eq1455 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1448 eq30
    | exact resolve eq30 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1469 : y = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1448 eq1106
    | exact resolve eq1106 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq1448
  have eq1472 : y = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1469
  have eq1488 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1455
    | exact resolve eq1455 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1455
  have eq1550 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1488 eq65
    | exact resolve eq65 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1772 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 X0 y
       have i₂ := eq1550
       grind)
    | exact superpose eq1550 eq61
    | exact resolve eq61 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1550
  have eq2177 : x = (τ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq343 x
       have i₂ := eq1772 x
       grind)
    | exact superpose eq1772 eq343
    | exact resolve eq343 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq2281 : x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq2177
       grind)
    | exact superpose eq2177 eq15
    | exact resolve eq15 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2308 : x = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2281
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2281
    | exact resolve eq2281 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq2325 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2308 eq1161
    | exact resolve eq1161 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq2308
  have eq2338 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2325
  have eq2345 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2338
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2338
    | exact resolve eq2338 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2347 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2345 eq28
    | exact resolve eq28 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2450 : y ≠ (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1472 eq2347
    | exact resolve eq2347 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472 eq2347
  have eq2451 : y ≠ (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2450
  have eq2452 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2451
       have r₂ := eq1488
       grind)
    | exact resolve eq2451 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488 eq2451
  have eq2454 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2452 eq21
    | exact resolve eq21 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2456 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq2452 eq57
    | exact resolve eq57 eq2452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2452
  have eq2483 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2454
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2454
    | exact resolve eq2454 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq2548 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq378 x X0
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq378
    | exact resolve eq378 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq2456
  have eq2561 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2548 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2548
    | (have j0 := eq2548 X0
       grind)
    | exact resolve eq2548 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq2947 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq67 eq2561
    | exact resolve eq2561 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2561
  have eq2993 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq2947 eq28
    | exact resolve eq28 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq3007 : x = y := by
    first
    | (have r₁ := eq2993
       have r₂ := eq2483
       grind)
    | exact resolve eq2993 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483 eq2993
  have eq3008 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3007
       grind)
    | exact superpose eq3007 eq19
    | exact resolve eq19 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3009 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3007
       grind)
    | exact superpose eq3007 eq25
    | exact resolve eq25 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3007
  have eq3033 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3009
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3009
    | exact resolve eq3009 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3009
  have eq3039 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3033 eq27
    | exact resolve eq27 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3033
  have eq3296 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3039 eq343
    | exact resolve eq343 eq3039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq3039
  have eq3306 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3296
       have i₂ := eq3008
       grind)
    | exact superpose eq3008 eq3296
    | exact resolve eq3296 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008 eq3296
  have eq3353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3306 eq15
    | exact resolve eq15 eq3306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3306
  have eq3390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3353
    | exact resolve eq3353 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3353
  have eq3401 : False := by grind
  exact eq3401

/-- `Equation2865`: `x = ((x ◇ (y ◇ x)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pxx_pxy_Equation2865 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2865 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2865.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq19
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq58 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq88 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
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
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | (have j0 := eq64 (τ X0) X1
       grind)
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq144 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq133
    | (have j0 := eq133 X0 X1
       grind)
    | exact resolve eq133 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq150 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq144
    | (have j0 := eq144 X0 X1
       grind)
    | exact resolve eq144 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq144
  have eq419 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq150 (σ X1) X0
       grind)
    | exact superpose eq150 eq24
    | (have j1 := eq150 (σ X1) X0
       grind)
    | exact resolve eq24 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq150
  have eq426 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq419
    | (have j0 := eq419 X0 X1
       grind)
    | exact resolve eq419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq436 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq426
    | (have j0 := eq426 X0 X1
       grind)
    | exact resolve eq426 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq635 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq694 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq635
    | (have j0 := eq635 X0 X1
       grind)
    | exact resolve eq635 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq699 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq88
    | (have j0 := eq88 X1 (σ X0)
       grind)
    | (have r₁ := eq88 X0 (σ X0)
       have r₂ := eq40 X0
       grind)
    | exact resolve eq88 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq706 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq5025 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq436 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq436 X0 X1
       grind)
    | exact superpose eq436 eq10
    | (have j1 := eq436 X0 X1
       grind)
    | exact resolve eq10 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq5077 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5025 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5025
    | (have j0 := eq5025 X0 X1
       grind)
    | exact resolve eq5025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5025
  have eq7455 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) (σ (τ X1)))) ∨ (σ X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X1
       have i₂ := eq5077 X0 (τ X1)
       grind)
    | (have i₁ := eq103 X0
       have i₂ := eq5077 (τ X0) X1
       grind)
    | exact superpose eq5077 eq103
    | (have j1 := eq5077 X0 (τ X1)
       grind)
    | exact resolve eq103 eq5077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq5077
  have eq7464 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (σ X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7455 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7455
    | (have j0 := eq7455 X0 X1
       grind)
    | exact resolve eq7455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7455
  have eq7476 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7464 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7464
    | (have j0 := eq7464 X0 X1
       grind)
    | exact resolve eq7464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7464
  have eq8663 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq7476 X0 X1
       grind)
    | exact superpose eq7476 eq11
    | (have j1 := eq7476 X0 X1
       grind)
    | exact resolve eq11 eq7476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7476
  have eq8743 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8663 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq8663
    | (have j0 := eq8663 X0 X1
       grind)
    | exact resolve eq8663 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8663
  have eq8800 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq8743 X0 (σ X1)
       grind)
    | exact superpose eq8743 eq15
    | (have j1 := eq8743 X0 (σ X1)
       grind)
    | exact resolve eq15 eq8743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8743
  have eq8872 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8800 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq8800
    | (have j0 := eq8800 X0 X1
       grind)
    | exact resolve eq8800 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8800
  have eq8888 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8872 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq8872
    | (have j0 := eq8872 X0 X1
       grind)
    | exact resolve eq8872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8872
  have eq10636 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8888 x y
       grind)
    | exact superpose eq8888 eq16
    | (have j1 := eq8888 x y
       grind)
    | exact resolve eq16 eq8888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8888
  have eq10699 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10636
       have i₂ := eq694 x y
       grind)
    | exact superpose eq694 eq10636
    | (have j1 := eq694 x y
       grind)
    | (have r₁ := eq10636
       have r₂ := eq694 x y
       grind)
    | (have r₁ := eq10636
       have r₂ := eq694 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq10636
       have r₂ := eq694 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10636 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq10636
  have eq10700 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10699
  have eq10701 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq10700
  have eq10882 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10701
       grind)
    | exact superpose eq10701 eq16
    | exact resolve eq16 eq10701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10701
  have eq10883 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq10882
       have r₂ := eq40 x
       grind)
    | exact resolve eq10882 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10882
  have eq10885 : y = (τ (σ x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10883
       grind)
    | exact superpose eq10883 eq10
    | exact resolve eq10 eq10883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10883
  have eq10957 : x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10885
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10885
    | exact resolve eq10885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10885
  have eq11177 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10957
       grind)
    | exact superpose eq10957 eq16
    | exact resolve eq16 eq10957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10957
  have eq11178 : (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq11177
       have r₂ := eq40 x
       grind)
    | exact resolve eq11177 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq11177
  have eq11181 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq11178
       grind)
    | exact superpose eq11178 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11178
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11178
       grind)
    | exact resolve eq12 eq11178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11206 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq706 y X0
       have i₂ := eq11178
       grind)
    | exact superpose eq11178 eq706
    | (have j0 := eq706 X0 x
       grind)
    | exact resolve eq706 eq11178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq11178
  have eq11465 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq11181 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq14665 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq11206 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11206
  have eq14670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14665
       have i₂ := eq11465
       grind)
    | exact superpose eq11465 eq14665
    | exact resolve eq14665 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11465 eq14665
  have eq14679 : False := by grind
  exact eq14679

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_pxx_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq47 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (k (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k x x) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 (M.op x x)) x) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq112 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq113 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq40 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40
    | exact resolve eq40 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 (M.op X0 X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq222 eq53
    | exact resolve eq53 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq223 eq53
    | exact resolve eq53 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq376 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 X0) X0
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq53
    | exact resolve eq53 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq530 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq285 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq285
    | (have j0 := eq285 X0 x
       grind)
    | exact resolve eq285 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq560 : (k (k x x) x) = (τ (k (k (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq50 eq530
    | exact resolve eq530 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq635 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq74 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq74 X0 X0
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq640 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq635 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq643 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq640 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq640 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq640 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq640 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq653 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq643
    | (have j0 := eq643 X0 X1
       grind)
    | exact resolve eq643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq6884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6884
    | exact resolve eq6884 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6884
  have eq6896 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq6885
       have r₂ := eq28
       grind)
    | exact resolve eq6885 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6885
  have eq6898 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6896
    | exact resolve eq6896 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6896
  have eq7033 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq6898
  have eq7068 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7033
    | exact resolve eq7033 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7033
  have eq7142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7068 eq92
    | exact resolve eq92 eq7068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7068
  have eq7150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7142
  have eq7152 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7150
       have r₂ := eq28
       grind)
    | exact resolve eq7150 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7150
  have eq7286 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7152
  have eq7321 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7286
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7286
    | exact resolve eq7286 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7286
  have eq7391 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq7321
       grind)
    | exact superpose eq7321 eq45
    | exact resolve eq45 eq7321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq7321
  have eq7405 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq7391
    | exact resolve eq7391 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7391
  have eq7550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7405 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq7405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7550
    | exact resolve eq7550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7550
  have eq7564 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7553
       have r₂ := eq28
       grind)
    | exact resolve eq7553 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7553
  have eq7566 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7564
    | exact resolve eq7564 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564
  have eq7567 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7566
  have eq7570 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7567
  have eq7605 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq7570
    | exact resolve eq7570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7570
  have eq7687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7605 eq7405
    | exact resolve eq7405 eq7605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7405 eq7605
  have eq7689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7687
  have eq7693 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7689
       have r₂ := eq28
       grind)
    | exact resolve eq7689 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7689
  have eq7695 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7693 eq28
    | exact resolve eq28 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7697 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7693 eq113
    | (have r₁ := eq113
       have r₂ := eq7693
       grind)
    | exact resolve eq113 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq7704 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7693 eq223
    | exact resolve eq223 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq7708 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7693 eq243
    | exact resolve eq243 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7711 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7697
  have eq7712 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq7708
    | exact resolve eq7708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7708
  have eq7714 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq7704
    | exact resolve eq7704 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7704
  have eq7718 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7693 eq7714
    | exact resolve eq7714 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7714
  have eq7739 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7718
  have eq7741 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7739 eq243
    | exact resolve eq243 eq7739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq7742 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq7768 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7693 eq7712
    | exact resolve eq7712 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7712
  have eq7795 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7768
  have eq7855 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7742 eq50
    | exact resolve eq50 eq7742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq7859 : (k (k x x) x) = (τ (k (M.op (σ x) (σ x)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7742 eq560
    | exact resolve eq560 eq7742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq7742
  have eq7865 : (k (k x x) x) = (τ (M.op (M.op (σ x) (σ x)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq7859
  have eq7889 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7739 eq7855
    | exact resolve eq7855 eq7739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7893 : (σ (k x (k x x))) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7855 eq43
    | exact resolve eq43 eq7855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq7855
  have eq7917 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq7889
  have eq7921 : (k (σ x) (k (σ x) (σ x))) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7893
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq7893
    | exact resolve eq7893 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893
  have eq7923 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq7917
    | exact resolve eq7917 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7917
  have eq7926 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq7923
       grind)
    | exact superpose eq7923 eq44
    | exact resolve eq44 eq7923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq7936 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq7923
       grind)
    | exact superpose eq7923 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq7923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923
  have eq7937 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq7936
  have eq7950 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7926
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq7926
    | exact resolve eq7926 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7926
  have eq7951 : (M.op (M.op x y) y) = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq240
       have i₂ := eq7937
       grind)
    | exact superpose eq7937 eq240
    | exact resolve eq240 eq7937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq7937
  have eq8283 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (k x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7950 eq48
    | exact resolve eq48 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq8284 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k x x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7950 eq49
    | exact resolve eq49 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq7950
  have eq8315 : ∀ X0 : G, (σ (k x X0)) = (σ (k (k x x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36 eq8284
    | exact resolve eq8284 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq8284
  have eq8316 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (k x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40 eq8283
    | exact resolve eq8283 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8283
  have eq20767 : (σ (k x (k x x))) = (σ (k (k x x) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8315 (k x x)
       have i₂ := eq8316 (k x x)
       grind)
    | exact superpose eq8316 eq8315
    | exact resolve eq8315 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315 eq8316
  have eq20819 : (σ (k x (k x x))) = (σ (k (k x x) x)) ∨ x = (M.op x y) := by grind
  clear eq20767
  have eq20857 : (σ (k x (k x x))) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20819
       have i₂ := eq157
       grind)
    | exact superpose eq157 eq20819
    | exact resolve eq20819 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20819
  have eq20876 : (k (σ x) (k (σ x) (σ x))) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20857
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq20857
    | exact resolve eq20857 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq20857
  have eq42400 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7711 eq59
    | exact resolve eq59 eq7711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq7711
  have eq45036 : (τ (σ x)) = (k (k x x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7795 eq7865
    | exact resolve eq7865 eq7795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7795 eq7865
  have eq45100 : (τ (σ x)) = (k (k x x) x) ∨ x = (M.op x y) := by grind
  clear eq45036
  have eq45105 : x = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq45100
    | exact resolve eq45100 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45100
  have eq45119 : (σ x) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157
       have i₂ := eq45105
       grind)
    | exact superpose eq45105 eq157
    | exact resolve eq157 eq45105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq45105
  have eq45149 : (σ x) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45119
    | exact resolve eq45119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45119
  have eq45425 : (σ x) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45149 eq20876
    | exact resolve eq20876 eq45149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20876 eq45149
  have eq45444 : (σ x) = (k (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq45425
  have eq45469 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45444 eq7921
    | exact resolve eq7921 eq45444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921 eq45444
  have eq45491 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq45469
  have eq61573 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7739 eq42400
    | exact resolve eq42400 eq7739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7739 eq42400
  have eq61687 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq61573
  have eq61696 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq61687
    | exact resolve eq61687 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61687
  have eq61713 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61696 eq53
    | exact resolve eq53 eq61696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61696
  have eq61775 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq61713
    | exact resolve eq61713 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61713
  have eq61860 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61775 eq7741
    | exact resolve eq7741 eq61775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7741 eq61775
  have eq61938 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq61860
  have eq61942 : x = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq61938
    | exact resolve eq61938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61938
  have eq61956 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq61942
       grind)
    | exact superpose eq61942 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq61942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61967 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq61956
  have eq61979 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61967
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61967
    | exact resolve eq61967 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61967
  have eq61980 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq61979
  have eq62016 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq61980
  have eq62100 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62016
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62016
    | exact resolve eq62016 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62016
  have eq63812 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61942
       have i₂ := eq62100
       grind)
    | exact superpose eq62100 eq61942
    | exact resolve eq61942 eq62100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61942 eq62100
  have eq63822 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq63812
  have eq63909 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63822 eq7693
    | exact resolve eq7693 eq63822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7693
  have eq64036 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq63909
  have eq64202 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64036 eq27
    | exact resolve eq27 eq64036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64203 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64036 eq30
    | exact resolve eq30 eq64036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq64036
  have eq64504 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq64203
    | exact resolve eq64203 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq64203
  have eq66595 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64202 eq45491
    | exact resolve eq45491 eq64202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45491 eq64202
  have eq66709 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq66595
  have eq67039 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63822 eq66709
    | exact resolve eq66709 eq63822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63822 eq66709
  have eq67068 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq67039
  have eq67773 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq67068 eq92
    | exact resolve eq92 eq67068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq67068
  have eq67804 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq67773
  have eq67823 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq67804
       have r₂ := eq7695
       grind)
    | exact resolve eq67804 eq7695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695 eq67804
  have eq68718 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq67823
       grind)
    | exact superpose eq67823 eq53
    | exact resolve eq53 eq67823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67823
  have eq68784 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68718
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68718
    | exact resolve eq68718 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68718
  have eq69876 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68784 eq7951
    | exact resolve eq7951 eq68784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7951 eq68784
  have eq69934 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq69876
  have eq69937 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69934
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69934
    | exact resolve eq69934 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69934
  have eq70070 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq69937
  have eq70072 : x = (M.op x y) := by
    first
    | (have r₁ := eq70070
       have r₂ := eq64504
       grind)
    | exact resolve eq70070 eq64504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64504 eq70070
  have eq70137 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq70072 eq21
    | exact resolve eq21 eq70072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq70145 : x ≠ x ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq70072 eq112
    | (have r₁ := eq112
       have r₂ := eq70072
       grind)
    | exact resolve eq112 eq70072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq70192 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq70072 eq222
    | exact resolve eq222 eq70072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq70234 : x = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq70145
  have eq70261 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq70192
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70192
    | exact resolve eq70192 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70192
  have eq70309 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq70137
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq70137
    | exact resolve eq70137 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70137
  have eq70319 : x = (M.op x x) := by
    first
    | exact superpose eq70072 eq70261
    | exact resolve eq70261 eq70072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70261
  have eq70327 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq70309 eq27
    | exact resolve eq27 eq70309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70777 : (k x x) = (M.op x x) := by grind
  have eq70860 : x = (k x x) := by
    first
    | (have i₁ := eq70777
       have i₂ := eq70319
       grind)
    | exact superpose eq70319 eq70777
    | exact resolve eq70777 eq70319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70777
  have eq71009 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq653 x x
       have i₂ := eq70860
       grind)
    | exact superpose eq70860 eq653
    | (have j0 := eq653 x x
       grind)
    | exact resolve eq653 eq70860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq70860
  have eq71012 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq71009
  have eq71013 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq71012
  have eq71027 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71013
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq71013
    | exact resolve eq71013 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71013
  have eq71041 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq70309 eq71027
    | exact resolve eq71027 eq70309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71027
  have eq95542 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70234
       have i₂ := eq70319
       grind)
    | exact superpose eq70319 eq70234
    | exact resolve eq70234 eq70319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70234
  have eq96278 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq637 x y
       have i₂ := eq95542
       grind)
    | exact superpose eq95542 eq637
    | (have j0 := eq637 x y
       grind)
    | exact resolve eq637 eq95542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95542
  have eq96282 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq96278
  have eq96291 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96282
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq96282
    | exact resolve eq96282 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96282
  have eq96310 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96291
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96291
    | exact resolve eq96291 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96291
  have eq96326 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq96310
    | exact resolve eq96310 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96310
  have eq96341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70309 eq96326
    | exact resolve eq96326 eq70309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96326
  have eq96351 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq96341
       have r₂ := eq28
       grind)
    | exact resolve eq96341 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96341
  have eq96358 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96351
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq96351
    | exact resolve eq96351 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96351
  have eq96365 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96358
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96358
    | exact resolve eq96358 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96358
  have eq96372 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70309 eq96365
    | exact resolve eq96365 eq70309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96365
  have eq96493 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq96372 eq376
    | exact resolve eq376 eq96372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96505 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq96372 eq53
    | exact resolve eq53 eq96372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq96582 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70327 eq96505
    | exact resolve eq96505 eq70327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96505
  have eq96590 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71041 eq96493
    | exact resolve eq96493 eq71041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96493
  have eq96604 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70327 eq96590
    | exact resolve eq96590 eq70327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96590
  have eq97292 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq96604
  have eq97394 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97292
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97292
    | exact resolve eq97292 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97292
  have eq97425 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70072 eq97394
    | exact resolve eq97394 eq70072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97394
  have eq97754 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq637 x y
       have i₂ := eq97425
       grind)
    | exact superpose eq97425 eq637
    | (have j0 := eq637 x y
       grind)
    | exact resolve eq637 eq97425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq97425
  have eq97758 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq97754
  have eq97767 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97758
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq97758
    | exact resolve eq97758 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97758
  have eq97784 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97767
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq97767
    | exact resolve eq97767 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97767
  have eq97800 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq97784
    | exact resolve eq97784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq97784
  have eq97815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70309 eq97800
    | exact resolve eq97800 eq70309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97800
  have eq97825 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq97815
       have r₂ := eq28
       grind)
    | exact resolve eq97815 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97815
  have eq97832 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97825
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq97825
    | exact resolve eq97825 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97825
  have eq97839 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97832
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq97832
    | exact resolve eq97832 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97832
  have eq97846 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70309 eq97839
    | exact resolve eq97839 eq70309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97839
  have eq98787 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97846 eq376
    | exact resolve eq376 eq97846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97846
  have eq98882 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71041 eq98787
    | exact resolve eq98787 eq71041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71041 eq98787
  have eq98895 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70327 eq98882
    | exact resolve eq98882 eq70327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70327 eq98882
  have eq98896 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq98895
  have eq98908 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq98896 eq28
    | exact resolve eq28 eq98896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq100199 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98896 eq96582
    | exact resolve eq96582 eq98896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96582 eq98896
  have eq100213 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq100199 eq96372
    | exact resolve eq96372 eq100199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96372 eq100199
  have eq100287 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq100213
  have eq100303 : x = (M.op y y) := by
    first
    | (have r₁ := eq100287
       have r₂ := eq98908
       grind)
    | exact resolve eq100287 eq98908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100287
  have eq100317 : y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq376 y
       have i₂ := eq100303
       grind)
    | exact superpose eq100303 eq376
    | exact resolve eq376 eq100303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq100303
  have eq100417 : y = (M.op x y) := by
    first
    | (have i₁ := eq100317
       have i₂ := eq70319
       grind)
    | exact superpose eq70319 eq100317
    | exact resolve eq100317 eq70319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70319 eq100317
  have eq100450 : y = (M.op x y) := by
    first
    | (have i₁ := eq100417
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100417
    | exact resolve eq100417 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq100417
  have eq100468 : x = y := by
    first
    | exact superpose eq70072 eq100450
    | exact resolve eq100450 eq70072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70072 eq100450
  have eq100502 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq100468
       grind)
    | exact superpose eq100468 eq25
    | exact resolve eq25 eq100468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq100468
  have eq100790 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq100502
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq100502
    | exact resolve eq100502 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq100502
  have eq100862 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq70309 eq100790
    | exact resolve eq100790 eq70309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70309 eq100790
  have eq100919 : False := by grind
  exact eq100919

/-- `Equation2891`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_y_pyx_x_pxy_Equation2891 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2891 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2891.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op X2 X3)) X3)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 (M.op X2 X3)) X3) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) X1 X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X1))) X2 X1
       have i₂ := eq9 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X1) = (M.op (M.op X0 y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op sF0 x)) x)
       have i₂ := eq9 X0 sF0 x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op y sF0))
       have i₂ := eq9 X0 y sF0
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op sF3 sF4))
       have i₂ := eq9 X0 sF3 sF4
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq84 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) y) = X0 := by
    intro X0
    first
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq81 eq9
    | exact resolve eq9 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq102 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq84 (M.op X0 (M.op sF0 x))
       have i₂ := eq9 X0 sF0 x
       grind)
    | exact superpose eq9 eq84
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq15
    | exact resolve eq15 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq133
    | exact resolve eq133 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq133
  have eq140 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140
    | (have j0 := eq140 x
       grind)
    | exact resolve eq140 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq134 X0
       grind)
    | exact superpose eq134 eq10
    | exact resolve eq10 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq246 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246
    | exact resolve eq246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq381 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq400 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op y (M.op x y)) (M.op X0 x))) := by
    intro X0 X1
    first
    | exact superpose eq78 eq55
    | exact resolve eq55 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq404 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X3)) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 (M.op (M.op X0 (M.op X2 X3)) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 y) x)) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq140 eq55
    | exact resolve eq55 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq413 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (M.op X0 X1) X1
       have i₂ := eq55 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 (M.op X1 X2)
       have i₂ := eq55 X0 X2 X1
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 x
       have i₂ := eq404 X0 (M.op (M.op X1 X0) X2) X2 x
       grind)
    | exact superpose eq404 eq53
    | exact resolve eq53 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq453 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X0 X3) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq446 X1 (M.op (M.op X0 (M.op X1 X2)) X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq446
    | exact resolve eq446 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op X3 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq446 (M.op X2 X1) (M.op (M.op X0 X1) X2) X3
       have i₂ := eq446 X1 X0 X2
       grind)
    | exact superpose eq446 eq446
    | exact resolve eq446 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op X0 X1) (M.op X1 x)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq446
    | exact resolve eq446 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq456 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq84 eq446
    | exact resolve eq446 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq463 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq446 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq446
    | (have j0 := eq446 y x X0
       grind)
    | exact resolve eq446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq446
    | (have j0 := eq446 (σ y) (σ x) X0
       grind)
    | exact resolve eq446 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op (M.op X3 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 (M.op X3 X2) (M.op (M.op X0 X2) X3)
       have i₂ := eq446 X2 X0 X3
       grind)
    | exact superpose eq446 eq55
    | exact resolve eq55 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x X1) (M.op X1 (M.op X0 y))) := by
    intro X0 X1
    first
    | exact superpose eq463 eq446
    | exact resolve eq446 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X1 (M.op X0 X1)) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq464 (M.op X1 (M.op x X1))
       have i₂ := eq55 sF4 X1 x
       grind)
    | exact superpose eq55 eq464
    | exact resolve eq464 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op X0 (M.op (M.op X0 X3) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq413 (M.op (M.op X0 X3) X2) (M.op X2 X3) X1
       have i₂ := eq446 X3 X0 X2
       grind)
    | exact superpose eq446 eq413
    | exact resolve eq413 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq463 eq413
    | exact resolve eq413 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq464 eq413
    | exact resolve eq413 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op (M.op X3 X1) X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op (M.op X3 X1) X3) X0
       have i₂ := eq413 X3 X1 X0
       grind)
    | exact superpose eq413 eq55
    | exact resolve eq55 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op (M.op X1 X0) X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq463 (M.op (M.op X0 X1) X0)
       have i₂ := eq413 X0 X1 sF0
       grind)
    | exact superpose eq413 eq463
    | exact resolve eq463 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq627 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op y X1) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 x
       have i₂ := eq506 (M.op x X0) (M.op sF0 X0) x y
       grind)
    | (have i₁ := eq624 X0 x
       have i₂ := eq506 y (M.op sF0 X0) x (M.op x X0)
       grind)
    | exact superpose eq506 eq624
    | exact resolve eq624 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq624
  have eq649 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | exact superpose eq595 eq555
    | exact resolve eq555 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq671 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq649 x x
       have i₂ := eq55 sF4 x x
       grind)
    | exact superpose eq55 eq649
    | exact resolve eq649 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq738 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X2 X3))) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X3 (M.op (M.op X0 X2) (M.op X2 X3))
       have i₂ := eq419 X0 X2 X3
       grind)
    | exact superpose eq419 eq55
    | exact resolve eq55 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 X3) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq446 X2 (M.op (M.op X0 X3) (M.op X3 X2)) X1
       have i₂ := eq419 X0 X3 X2
       grind)
    | exact superpose eq419 eq446
    | exact resolve eq446 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq1269 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X3) (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 (M.op X0 (M.op X2 X3)) X3 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1271 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 (M.op X0 X2) X3 (M.op X3 X2)
       have i₂ := eq446 X2 X0 X3
       grind)
    | exact superpose eq446 eq54
    | exact resolve eq54 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ y)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq93 eq54
    | exact resolve eq54 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1323 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X2 X1) X4))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 X4 (M.op X0 (M.op (M.op X2 X1) X4))
       have i₂ := eq54 X0 X2 X1 X4
       grind)
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X1) X3)) = (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq446 X3 (M.op X0 (M.op (M.op X2 X1) X3)) X4
       have i₂ := eq54 X0 X2 X1 X3
       grind)
    | exact superpose eq54 eq446
    | exact resolve eq446 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2347 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op x y))) = (M.op X2 (M.op y (M.op (M.op X0 X1) (M.op X1 x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq455 eq55
    | exact resolve eq55 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq2382 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op x y))) = (M.op X2 (M.op y (M.op x X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq2347 X0 x X2
       have i₂ := eq738 X0 y x x
       grind)
    | exact superpose eq738 eq2347
    | exact resolve eq2347 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347
  have eq2927 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq381
    | (have j0 := eq381 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq381 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq3493 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op (M.op y (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq400 (M.op x X1) X1
       have i₂ := eq413 x X1 (M.op y sF0)
       grind)
    | exact superpose eq413 eq400
    | exact resolve eq400 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq3802 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X0 X1)) = (M.op (M.op x y) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (M.op y X1) X0
       have i₂ := eq413 y X1 X0
       grind)
    | exact superpose eq413 eq539
    | exact resolve eq539 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3821 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 y))) = (M.op X1 (M.op (M.op (M.op x y) X0) (M.op x X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq413 (M.op x X2) (M.op X2 (M.op X0 y)) X1
       have i₂ := eq539 X0 X2
       grind)
    | exact superpose eq539 eq413
    | exact resolve eq413 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq4009 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 y) x)) = (M.op X1 (M.op x (M.op (M.op x y) (M.op X0 (M.op (M.op x y) y))))) := by
    intro X0 X1
    first
    | exact superpose eq77 eq593
    | exact resolve eq593 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq4010 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op x (M.op (M.op x y) (M.op X0 (M.op (M.op X2 X1) y))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq593 X3 (M.op X0 (M.op (M.op X2 X1) y))
       have i₂ := eq54 X0 X2 X1 y
       grind)
    | exact superpose eq54 eq593
    | exact resolve eq593 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4027 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y (M.op x (M.op (M.op x y) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 y X0
       have i₂ := eq593 y X0
       grind)
    | exact superpose eq593 eq55
    | exact resolve eq55 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4028 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op x (M.op (M.op x y) (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq413 y X1 X0
       have i₂ := eq593 X0 (M.op y X1)
       grind)
    | exact superpose eq593 eq413
    | exact resolve eq413 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq4157 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op x (M.op (M.op x y) (M.op X0 (M.op x (M.op (M.op x y) (M.op X2 X1))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4010 X0 X1 X2 X3
       have i₂ := eq593 X0 (M.op X2 X1)
       grind)
    | exact superpose eq593 eq4010
    | exact resolve eq4010 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010
  have eq4158 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op x (M.op (M.op x y) (M.op X0 (M.op (M.op x y) y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4009 X0 X1
       have i₂ := eq407 X0 X1
       grind)
    | (have i₁ := eq4009 x X1
       have i₂ := eq407 x X1
       grind)
    | exact superpose eq407 eq4009
    | exact resolve eq4009 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq4009
  have eq4205 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op x (M.op (M.op x y) (M.op X0 (M.op x (M.op (M.op x y) (M.op X3 (M.op X2 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq404 X0 X1 X2 X3
       have i₂ := eq4157 X0 (M.op X2 X3) X3 X1
       grind)
    | exact superpose eq4157 eq404
    | exact resolve eq404 eq4157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq4157
  have eq4297 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op x (M.op (M.op x y) (M.op X0 (M.op x (M.op (M.op x y) X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4205 X0 X1 X2 X1
       have i₂ := eq55 sF0 X1 X2
       grind)
    | exact superpose eq55 eq4205
    | exact resolve eq4205 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205
  have eq4423 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 X2)))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq595 eq54
    | exact resolve eq54 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4528 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1276 eq4423
    | exact resolve eq4423 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4423
  have eq4584 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 X2))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4528 X0 X1 X2
       have i₂ := eq4297 sF2 (M.op X0 sF4) (M.op sF2 (M.op sF4 (M.op X1 X2)))
       grind)
    | exact superpose eq4297 eq4528
    | exact resolve eq4528 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528
  have eq4620 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 X2))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4584 X1 X1 X2
       have i₂ := eq1271 sF4 X1 (M.op sF0 (M.op sF2 (M.op x (M.op sF0 (M.op sF2 (M.op sF4 (M.op X1 X2))))))) x
       grind)
    | (have i₁ := eq4584 X1 X1 X2
       have i₂ := eq1271 x X1 (M.op sF0 (M.op sF2 (M.op x (M.op sF0 (M.op sF2 (M.op sF4 (M.op X1 X2))))))) sF4
       grind)
    | exact superpose eq1271 eq4584
    | exact resolve eq4584 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4584
  have eq4651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X3 X1)) = (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op X1 X2)))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq453 X0 X1 X2 X3
       have i₂ := eq4620 X0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq4620 eq453
    | exact resolve eq453 eq4620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq4620
  have eq4936 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X3 X1)) = (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4651 X0 x X1 X3
       have i₂ := eq55 sF4 X1 x
       grind)
    | exact superpose eq55 eq4651
    | exact resolve eq4651 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4651
  have eq6882 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op x y) (M.op y (M.op x X0)))) := by
    intro X0 X1
    first
    | exact superpose eq2382 eq55
    | exact resolve eq55 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6902 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op X0 (M.op x (M.op y (M.op x (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq2382 eq593
    | exact resolve eq593 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6967 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op x (M.op (M.op x y) (M.op X0 (M.op x (M.op y (M.op x (M.op x y)))))))) := by
    intro X0 X1
    first
    | exact superpose eq6902 eq4158
    | exact resolve eq4158 eq6902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158
  have eq7392 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) (M.op x y)) = (M.op (σ x) (M.op (M.op X0 (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq464 eq456
    | exact resolve eq456 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7393 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) y)) := by
    intro X0
    first
    | exact superpose eq671 eq456
    | exact resolve eq456 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq7404 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X1 y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq456 eq55
    | exact resolve eq55 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7418 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (σ (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq134 (M.op y y)
       have i₂ := eq456 y y
       grind)
    | exact superpose eq456 eq134
    | exact resolve eq134 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7441 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq7418
       have i₂ := eq134 y
       grind)
    | exact superpose eq134 eq7418
    | exact resolve eq7418 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7418
  have eq7453 : ∀ X0 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op (M.op x y) (M.op y X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq7404 X0 X2 X2
       have i₂ := eq738 X0 sF0 X2 y
       grind)
    | exact superpose eq738 eq7404
    | (have j1 := eq738 x X2 y X0
       grind)
    | exact resolve eq7404 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7404
  have eq7459 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7393 X0
       have i₂ := eq593 sF2 (M.op sF2 (M.op sF4 X0))
       grind)
    | exact superpose eq593 eq7393
    | exact resolve eq7393 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7393
  have eq7460 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (M.op x y) (M.op X0 (σ y))))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7392 X0
       have i₂ := eq593 sF2 (M.op X0 sF3)
       grind)
    | exact superpose eq593 eq7392
    | exact resolve eq7392 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392
  have eq7503 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))))))))) := by
    first
    | (have i₁ := eq7441
       have i₂ := eq4936 (σ y) (σ y) (σ y)
       grind)
    | exact superpose eq4936 eq7441
    | exact resolve eq7441 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936 eq7441
  have eq7522 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) = (M.op (σ x) (M.op x (M.op (M.op x y) (M.op X0 (σ y))))) := by
    intro X0
    first
    | exact superpose eq7459 eq7460
    | exact resolve eq7460 eq7459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7459 eq7460
  have eq7561 : (M.op (M.op (σ y) x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))))))))) = (σ (M.op (M.op y x) (M.op x y))) := by
    first
    | (have i₁ := eq7503
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7503
    | exact resolve eq7503 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7503
  have eq7603 : (M.op (M.op (σ y) x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ y) (σ y)))))))) = (σ (M.op (M.op y x) (M.op x y))) := by
    first
    | exact superpose eq7522 eq7561
    | exact resolve eq7561 eq7522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7522 eq7561
  have eq8095 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq595 eq1276
    | exact resolve eq1276 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8198 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8095 X0 X1
       have i₂ := eq4297 sF2 (M.op X0 sF4) (M.op sF2 (M.op sF4 X1))
       grind)
    | exact superpose eq4297 eq8095
    | exact resolve eq8095 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095
  have eq8251 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) (σ y)) = (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8198 X1 X1
       have i₂ := eq1271 sF4 X1 (M.op sF0 (M.op sF2 (M.op x (M.op sF0 (M.op sF2 (M.op sF4 X1)))))) x
       grind)
    | (have i₁ := eq8198 X1 X1
       have i₂ := eq1271 x X1 (M.op sF0 (M.op sF2 (M.op x (M.op sF0 (M.op sF2 (M.op sF4 X1)))))) sF4
       grind)
    | exact superpose eq1271 eq8198
    | exact resolve eq8198 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8299 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op X1 (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq1276 eq8251
    | exact resolve eq8251 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq8251
  have eq8339 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op X1 (σ y)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8299 X0 X1
       have i₂ := eq4297 sF2 (M.op X0 sF4) (M.op X1 sF3)
       grind)
    | exact superpose eq4297 eq8299
    | exact resolve eq8299 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8299
  have eq8374 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) = (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op X1 (σ y)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8339 X1 X1
       have i₂ := eq1271 sF4 X1 (M.op sF0 (M.op sF2 (M.op x (M.op sF0 (M.op X1 sF3))))) x
       grind)
    | (have i₁ := eq8339 X1 X1
       have i₂ := eq1271 x X1 (M.op sF0 (M.op sF2 (M.op x (M.op sF0 (M.op X1 sF3))))) sF4
       grind)
    | exact superpose eq1271 eq8339
    | exact resolve eq8339 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8339
  have eq9029 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op x y) (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq102 eq3802
    | exact resolve eq3802 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq9107 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op x X1) X1 X0
       have i₂ := eq3802 X1 (M.op X0 X1)
       grind)
    | (have i₁ := eq55 (M.op x y) y x
       have i₂ := eq3802 X0 (M.op x y)
       grind)
    | exact superpose eq3802 eq55
    | exact resolve eq55 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9229 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op x y) (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | (have i₁ := eq9029 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9029
    | (have j0 := eq9029 X0
       grind)
    | exact resolve eq9029 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9029
  have eq14360 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op (M.op x y) (M.op y X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq446 x X0 X1
       have i₂ := eq7453 X1 (M.op (M.op X0 x) X1)
       grind)
    | exact superpose eq7453 eq446
    | exact resolve eq446 eq7453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7453
  have eq14886 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op (M.op x y) (M.op y (M.op (M.op X0 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3802 X0 X1
       have i₂ := eq9107 (M.op X0 X1) X0
       grind)
    | exact superpose eq9107 eq3802
    | exact resolve eq3802 eq9107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802
  have eq14907 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x X1)) = (M.op X2 (M.op X0 (M.op (M.op x y) (M.op y (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 X0 (M.op x X1)
       have i₂ := eq9107 X0 X1
       grind)
    | exact superpose eq9107 eq55
    | exact resolve eq55 eq9107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14959 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op X1 X0))) = (M.op X2 (M.op y (M.op x (M.op (M.op x X0) X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq9107 eq4027
    | exact resolve eq4027 eq9107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9107
  have eq15248 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op X0 (M.op x (M.op (M.op x y) (M.op X0 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq14886 X0 X1
       have i₂ := eq4297 X0 y (M.op X0 X1)
       grind)
    | exact superpose eq4297 eq14886
    | exact resolve eq14886 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14886
  have eq15482 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op (M.op x y) (M.op X0 (M.op x (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | exact superpose eq4027 eq15248
    | exact resolve eq15248 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15248
  have eq15665 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op X1 (σ y)))))))) = (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op y (M.op (M.op (σ x) (σ y)) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq15482 eq8374
    | exact resolve eq8374 eq15482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8374
  have eq16003 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x X1)) = (M.op (M.op X0 x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (M.op x (M.op (M.op x y) (M.op X1 (σ y)))))))) := by
    intro X0 X1
    first
    | exact superpose eq14907 eq15665
    | exact resolve eq15665 eq14907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907 eq15665
  have eq16144 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) x) (M.op x (σ y))) := by
    first
    | exact superpose eq16003 eq7603
    | exact resolve eq7603 eq16003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603 eq16003
  have eq16361 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op x (M.op (M.op x y) (M.op y X0))))) = (M.op X1 (M.op (M.op (M.op x y) x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq9229 eq4027
    | exact resolve eq4027 eq9229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9229
  have eq16409 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op (M.op (M.op x y) x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq4027 eq16361
    | exact resolve eq16361 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16361
  have eq18129 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op x X1)) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq14360 eq6882
    | exact resolve eq6882 eq14360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6882 eq14360
  have eq18625 : ∀ X0 X1 : G, (M.op (M.op X1 x) (M.op x y)) = (M.op (M.op X1 (M.op (M.op X0 x) (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X1 (M.op (M.op X0 x) (M.op x y))
       have i₂ := eq18129 X0 y
       grind)
    | exact superpose eq18129 eq456
    | exact resolve eq456 eq18129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq18129
  have eq18650 : ∀ X0 X1 : G, (M.op (M.op X1 x) (M.op x y)) = (M.op (M.op X1 (M.op y X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18625 X0 X1
       have i₂ := eq738 X0 X1 x y
       grind)
    | exact superpose eq738 eq18625
    | exact resolve eq18625 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18625
  have eq20830 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op y X2))) = (M.op X1 (M.op X2 (M.op (M.op X0 x) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X2 (M.op X0 (M.op y X2))
       have i₂ := eq18650 X2 X0
       grind)
    | exact superpose eq18650 eq55
    | exact resolve eq55 eq18650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18650
  have eq20945 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op y X2))) = (M.op X1 (M.op X2 (M.op y (M.op x (M.op X0 x))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2382 eq20830
    | exact resolve eq20830 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20830
  have eq21072 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op y X2))) = (M.op X1 (M.op X2 (M.op y X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20945 X0 X1 X2
       have i₂ := eq55 y x X0
       grind)
    | exact superpose eq55 eq20945
    | exact resolve eq20945 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20945
  have eq24570 : (M.op (M.op y x) (M.op x y)) = (τ (M.op (M.op (σ y) x) (M.op x (σ y)))) := by
    first
    | exact superpose eq16144 eq10
    | exact resolve eq10 eq16144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26901 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (τ (M.op (M.op (σ y) X0) (M.op X0 (M.op (M.op x (σ y)) x)))) := by
    intro X0
    first
    | (have i₁ := eq24570
       have i₂ := eq454 sF3 x (M.op x sF3) x
       grind)
    | exact superpose eq454 eq24570
    | exact resolve eq24570 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq24570
  have eq27140 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (τ (M.op (M.op (σ y) X0) (M.op X0 (M.op x (M.op (M.op x y) (M.op x (M.op x (M.op (M.op x y) (M.op x (σ y)))))))))) := by
    intro X0
    first
    | (have i₁ := eq26901 x
       have i₂ := eq4297 x x (M.op x sF3)
       grind)
    | exact superpose eq4297 eq26901
    | exact resolve eq26901 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26901
  have eq27432 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (τ (M.op (M.op (σ y) X0) (M.op X0 (M.op x (M.op (M.op x y) (M.op y (σ y))))))) := by
    intro X0
    first
    | exact superpose eq15482 eq27140
    | exact resolve eq27140 eq15482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15482 eq27140
  have eq27652 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (τ (M.op (M.op (σ y) X0) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq4028 eq27432
    | exact resolve eq27432 eq4028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028 eq27432
  have eq29575 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (τ (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq595 eq27652
    | exact resolve eq27652 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27652
  have eq31876 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) x) X0) X1) = (M.op x (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq168 eq1269
    | exact resolve eq1269 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq31886 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1269 X0 x X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1269
    | (have j0 := eq1269 X0 x X1 y
       grind)
    | exact resolve eq1269 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32046 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 (M.op (M.op X3 X1) X2))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq446 X1 X0 X3
       have i₂ := eq1269 X3 (M.op X0 X1) (M.op X3 X1) X2
       grind)
    | exact superpose eq1269 eq446
    | exact resolve eq446 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32058 : ∀ X0 : G, (M.op (M.op (σ y) x) (M.op x (σ y))) = (σ (M.op (M.op y X0) (M.op x (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq16144
       have i₂ := eq1269 x y sF0 x
       grind)
    | exact superpose eq1269 eq16144
    | exact resolve eq16144 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16144
  have eq32150 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op y X0) X1)) = (M.op X2 (M.op x (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3493 (M.op X0 (M.op X2 sF0)) X1
       have i₂ := eq1269 X0 y X2 sF0
       grind)
    | exact superpose eq1269 eq3493
    | exact resolve eq3493 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3493
  have eq32185 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X4 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq446 (M.op X1 (M.op X2 X3)) (M.op X0 X3) X4
       have i₂ := eq1269 X1 X0 X2 X3
       grind)
    | exact superpose eq1269 eq446
    | exact resolve eq446 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq32214 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X2 X1) (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32185 X0 X1 X2 X3 x
       have i₂ := eq1327 X0 X1 X2 (M.op X1 (M.op X2 X3)) x
       grind)
    | exact superpose eq1327 eq32185
    | exact resolve eq32185 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq32185
  have eq54889 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X0 (M.op x (M.op (M.op x y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31886 X0 X1
       have i₂ := eq593 X0 X1
       grind)
    | exact superpose eq593 eq31886
    | exact resolve eq31886 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq54973 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op x (M.op x X0)))) = (M.op X1 (M.op (M.op x y) (M.op X0 (M.op (M.op x y) y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2382 (M.op x X0) x
       have i₂ := eq31886 X0 sF0
       grind)
    | exact superpose eq31886 eq2382
    | exact resolve eq2382 eq31886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31886
  have eq55040 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op x (M.op x X0)))) = (M.op X1 (M.op (M.op x y) (M.op X0 (M.op x (M.op y (M.op x (M.op x y))))))) := by
    intro X0 X1
    first
    | exact superpose eq6902 eq54973
    | exact resolve eq54973 eq6902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6902 eq54973
  have eq55116 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op X1 X0))) = (M.op X2 (M.op y (M.op x (M.op (M.op x y) (M.op X0 (M.op x (M.op (M.op x y) X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14959 X0 X1 X2
       have i₂ := eq54889 X0 X1
       grind)
    | exact superpose eq54889 eq14959
    | exact resolve eq14959 eq54889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14959 eq54889
  have eq55369 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op x (M.op y (M.op x (M.op x X0))))) := by
    intro X0 X1
    first
    | exact superpose eq55040 eq6967
    | exact resolve eq6967 eq55040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6967 eq55040
  have eq55524 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op X1 X0))) = (M.op X2 (M.op X0 (M.op x (M.op (M.op x y) X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4027 eq55116
    | exact resolve eq55116 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4027 eq55116
  have eq55952 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op x (M.op (M.op x y) (M.op X0 (M.op x (M.op x (M.op y (M.op x (M.op x X2))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55369 eq4297
    | exact resolve eq4297 eq55369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297
  have eq55979 : ∀ X0 : G, (M.op (M.op (σ y) x) (M.op x (σ y))) = (σ (M.op (M.op y X0) (M.op x (M.op x (M.op y (M.op x (M.op x X0))))))) := by
    intro X0
    first
    | exact superpose eq55369 eq32058
    | exact resolve eq32058 eq55369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32058
  have eq57127 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op X1 X0))) = (M.op X2 (M.op X0 (M.op x (M.op x (M.op y (M.op x (M.op x X1))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55369 eq55524
    | exact resolve eq55524 eq55369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55524
  have eq57985 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op x (M.op x (M.op y (M.op x (M.op x (M.op X0 (M.op x (M.op x (M.op y (M.op x (M.op x X2)))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55369 eq55952
    | exact resolve eq55952 eq55369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55952
  have eq59420 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op X0 X1))) = (M.op X2 (M.op (M.op (M.op x y) X0) (M.op x X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16409 (M.op x X2) X1
       have i₂ := eq1271 x sF0 X2 x
       grind)
    | (have i₁ := eq16409 (M.op X0 X2) X1
       have i₂ := eq1271 X0 sF0 X2 x
       grind)
    | exact superpose eq1271 eq16409
    | exact resolve eq16409 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16409
  have eq59491 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 y))) = (M.op X1 (M.op y (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq59420 eq3821
    | exact resolve eq3821 eq59420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821 eq59420
  have eq61439 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op x y) X1)) = (M.op X2 (M.op X0 (M.op y (M.op x (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2382 eq585
    | exact resolve eq585 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61502 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) X0) (M.op X1 (M.op (M.op X1 (M.op X2 X0)) (M.op y X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq585 X0 (M.op sF0 X0) (M.op y X1) (M.op X1 X0)
       grind)
    | exact superpose eq585 eq627
    | exact resolve eq627 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq61645 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) X0) (M.op X1 (M.op X2 (M.op y (M.op X1 (M.op X2 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61502 X0 X1 X2
       have i₂ := eq21072 (M.op X1 (M.op X2 X0)) X1 X2
       grind)
    | (have i₁ := eq61502 X0 X1 X2
       have i₂ := eq21072 X2 X1 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq21072 eq61502
    | exact resolve eq61502 eq21072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21072 eq61502
  have eq61727 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x (M.op y (M.op x (M.op x X1))))) = (M.op X2 (M.op X0 (M.op y (M.op x (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55369 eq61439
    | exact resolve eq61439 eq55369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61439
  have eq62066 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op X0 (M.op (M.op (M.op X1 X2) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq585 (M.op (M.op X1 X2) X1) X0 X2 X3
       have i₂ := eq615 (M.op (M.op (M.op X1 X2) X1) X3) X2 X0 X1
       grind)
    | exact superpose eq615 eq585
    | exact resolve eq585 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq63148 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X2 (M.op (M.op (M.op X4 X1) X4) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1323 X2 X4 (M.op X4 X1) X3 X0
       have i₂ := eq738 X2 X0 X4 X1
       grind)
    | exact superpose eq738 eq1323
    | exact resolve eq1323 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq63223 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y (M.op x X2))) = (M.op X0 (M.op (M.op (M.op x y) X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2382 x X1
       have i₂ := eq738 sF0 X1 X2 x
       grind)
    | exact superpose eq738 eq2382
    | exact resolve eq2382 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq63412 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op X1 X0))) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63148 X2 X1 X0 X3 x
       have i₂ := eq62066 X0 x X1 X2
       grind)
    | exact superpose eq62066 eq63148
    | exact resolve eq63148 eq62066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62066 eq63148
  have eq64412 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (σ y))) = (M.op (M.op X0 X2) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq595 (M.op X0 X1) X1
       have i₂ := eq740 X0 X1 sF3 x
       grind)
    | (have i₁ := eq595 (M.op X0 x) x
       have i₂ := eq740 X0 X1 sF3 x
       grind)
    | exact superpose eq740 eq595
    | exact resolve eq595 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq740
  have eq67762 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op (M.op X4 (M.op X3 (M.op X2 X1))) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq585 X4 X0 (M.op X2 X3) (M.op X3 (M.op X2 X1))
       have i₂ := eq32214 X0 X3 X2 X1
       grind)
    | exact superpose eq32214 eq585
    | exact resolve eq585 eq32214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32214
  have eq67917 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X3 (M.op X2 (M.op X4 (M.op X3 (M.op X2 X1))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67762 X0 X1 X2 X3 X4
       have i₂ := eq63412 X3 X2 (M.op X4 (M.op X3 (M.op X2 X1))) X4
       grind)
    | (have i₁ := eq67762 X0 X1 X2 X3 X4
       have i₂ := eq63412 (M.op X4 (M.op X3 (M.op X2 X1))) X2 X3 X4
       grind)
    | exact superpose eq63412 eq67762
    | exact resolve eq67762 eq63412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63412 eq67762
  have eq71445 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op X0 (M.op y (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq585 X1 X0 y X2
       have i₂ := eq59491 (M.op X1 X2) X0 X1
       grind)
    | (have i₁ := eq585 y X1 X2 x
       have i₂ := eq59491 (M.op y x) X1 X2
       grind)
    | exact superpose eq59491 eq585
    | exact resolve eq585 eq59491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq59491
  have eq71735 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op X0 (M.op X1 (M.op x (M.op x (M.op y (M.op x (M.op x (M.op X1 X2)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71445 X0 X1 X2
       have i₂ := eq57127 X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq57127 eq71445
    | exact resolve eq71445 eq57127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57127 eq71445
  have eq76796 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) x) X0) X1) = (M.op x (M.op X0 (M.op y (M.op x X1)))) := by
    intro X0 X1
    first
    | exact superpose eq2382 eq31876
    | exact resolve eq31876 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq77229 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X1 (M.op x y)))) = (M.op x (M.op X0 (M.op y (M.op x X1)))) := by
    intro X0 X1
    first
    | exact superpose eq76796 eq31876
    | exact resolve eq31876 eq76796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31876 eq76796
  have eq107074 : ∀ X0 : G, (M.op (M.op y x) (M.op x y)) = (τ (M.op (M.op (σ y) X0) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq64412 eq29575
    | exact resolve eq29575 eq64412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29575 eq64412
  have eq111625 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op x (M.op X1 (M.op (M.op X0 X2) (M.op x y))))) = (M.op X3 (M.op (M.op y X0) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32150 X1 (M.op X0 X2) X3
       have i₂ := eq1271 X1 y X2 X0
       grind)
    | (have i₁ := eq32150 X1 (M.op X0 X2) X3
       have i₂ := eq1271 X0 y X2 X1
       grind)
    | exact superpose eq1271 eq32150
    | exact resolve eq32150 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq32150
  have eq112138 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op y X0) (M.op X1 X2))) = (M.op X3 (M.op x (M.op X1 (M.op y (M.op x (M.op X0 X2)))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq77229 eq111625
    | exact resolve eq111625 eq77229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111625
  have eq140743 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2927 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2927
    | (have j0 := eq2927 x y
       grind)
    | exact resolve eq2927 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq140787 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq20 eq140743
    | exact resolve eq140743 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140743
  have eq140788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq140787
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140787
    | exact resolve eq140787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140787
  have eq140789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq140788
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140788
    | exact resolve eq140788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140788
  have eq140790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq26 eq140789
    | exact resolve eq140789 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140789
  have eq140791 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq140790
       have r₂ := eq27
       grind)
    | exact resolve eq140790 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140790
  have eq140792 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq140791
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140791
    | exact resolve eq140791 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140791
  have eq140793 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq140792
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140792
    | exact resolve eq140792 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140792
  have eq140794 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq26 eq140793
    | exact resolve eq140793 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140793
  have eq140795 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq140794
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140794
    | exact resolve eq140794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140794
  have eq140796 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq140795
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140795
    | exact resolve eq140795 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140795
  have eq140817 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq140796 eq289
    | exact resolve eq289 eq140796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140796
  have eq140978 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq39 eq140817
    | exact resolve eq140817 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq140817
  have eq141069 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq140978
       have i₂ := eq289 sF2
       grind)
    | exact superpose eq289 eq140978
    | exact resolve eq140978 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq140978
  have eq141138 : (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq38 eq141069
    | exact resolve eq141069 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141069
  have eq141139 : (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq141138
  have eq141210 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq141139
       grind)
    | exact superpose eq141139 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq141139
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq141139
       grind)
    | exact resolve eq12 eq141139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141212 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq134 y
       have i₂ := eq141139
       grind)
    | exact superpose eq141139 eq134
    | exact resolve eq134 eq141139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141139
  have eq141377 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq141212
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq141212
    | exact resolve eq141212 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141212
  have eq141448 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq141377
       have i₂ := eq134 x
       grind)
    | exact superpose eq134 eq141377
    | exact resolve eq141377 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq141377
  have eq141501 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq141448
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq141448
    | exact resolve eq141448 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141448
  have eq141726 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq141501 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq141501
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq141501
       grind)
    | exact resolve eq12 eq141501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141501
  have eq327926 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq141210 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141210
  have eq327931 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq327926
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq327926
    | exact resolve eq327926 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327926
  have eq358616 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq141726 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141726
  have eq358617 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59 eq358616
    | exact resolve eq358616 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq358616
  have eq358618 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq358617
    | exact resolve eq358617 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358617
  have eq358620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq358618
       have i₂ := eq327931
       grind)
    | exact superpose eq327931 eq358618
    | exact resolve eq358618 eq327931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327931 eq358618
  have eq358721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq358620
  have eq358729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq358721
    | exact resolve eq358721 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358721
  have eq358733 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq358729
       have r₂ := eq27
       grind)
    | exact resolve eq358729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358729
  have eq358737 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq358733 eq464
    | exact resolve eq464 eq358733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq358733
  have eq363103 : (τ (σ x)) = (M.op (M.op y x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq358737 eq107074
    | exact resolve eq107074 eq358737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107074 eq358737
  have eq363769 : x = (M.op (M.op y x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq363103
    | exact resolve eq363103 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq363103
  have eq364141 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op (M.op X0 x) (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq363769 eq32046
    | exact resolve eq32046 eq363769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32046 eq363769
  have eq364478 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op y (M.op x (M.op X0 x))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq77229 eq364141
    | exact resolve eq364141 eq77229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77229 eq364141
  have eq364547 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op y X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq364478 X0
       have i₂ := eq55 y x X0
       grind)
    | exact superpose eq55 eq364478
    | exact resolve eq364478 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364478
  have eq364569 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq364547 x
       have i₂ := eq55 x x y
       grind)
    | exact superpose eq55 eq364547
    | exact resolve eq364547 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq364547
  have eq364580 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq364569
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq364569
    | exact resolve eq364569 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq364569
  have eq364581 : y = (M.op x y) := by grind
  clear eq364580
  have eq364587 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq364581 eq20
    | exact resolve eq20 eq364581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq365171 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op x (M.op y (M.op x (M.op x X0))))) := by
    intro X0 X1
    first
    | exact superpose eq364581 eq55369
    | exact resolve eq55369 eq364581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55369
  have eq365325 : ∀ X0 X1 X2 : G, x = (M.op (M.op y X0) (M.op X1 (M.op X2 (M.op y (M.op X1 (M.op X2 X0)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq364581 eq61645
    | exact resolve eq61645 eq364581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61645
  have eq365329 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op y X1) (M.op X1 X2))) = (M.op X0 (M.op y (M.op x X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq364581 eq63223
    | exact resolve eq63223 eq364581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63223 eq364581
  have eq367169 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y (M.op x X2))) = (M.op X0 (M.op x (M.op X1 (M.op y (M.op x (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365329 X0 X1 X2
       have i₂ := eq112138 X1 X1 X2 X0
       grind)
    | exact superpose eq112138 eq365329
    | exact resolve eq365329 eq112138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112138 eq365329
  have eq367171 : (σ x) = (M.op (M.op (σ y) x) (M.op x (σ y))) := by
    first
    | (have i₁ := eq55979 x
       have i₂ := eq365325 x x x
       grind)
    | exact superpose eq365325 eq55979
    | exact resolve eq55979 eq365325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55979 eq365325
  have eq367198 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y X1)) = (M.op X2 (M.op X0 (M.op y (M.op x (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61727 X0 X1 X2
       have i₂ := eq365171 X1 X2
       grind)
    | exact superpose eq365171 eq61727
    | exact resolve eq61727 eq365171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61727
  have eq367295 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op x (M.op x (M.op y (M.op x (M.op x (M.op X0 (M.op x (M.op y X2))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57985 X0 X1 X2
       have i₂ := eq365171 X2 x
       grind)
    | exact superpose eq365171 eq57985
    | exact resolve eq57985 eq365171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57985
  have eq367327 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op X0 (M.op X1 (M.op x (M.op y (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71735 X0 X1 X2
       have i₂ := eq365171 (M.op X1 X2) x
       grind)
    | exact superpose eq365171 eq71735
    | exact resolve eq71735 eq365171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71735 eq365171
  have eq367537 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq364587
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq364587
    | exact resolve eq364587 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq364587
  have eq367597 : (σ x) = (M.op (M.op (σ y) x) (M.op x (σ y))) := by
    first
    | (have i₁ := eq367171
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq367171
    | exact resolve eq367171 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq367171
  have eq367712 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op y (M.op x (M.op X0 (M.op x (M.op y X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq367295 X0 X1 X2
       have i₂ := eq367327 X1 x (M.op x (M.op X0 (M.op x (M.op y X2))))
       grind)
    | exact superpose eq367327 eq367295
    | exact resolve eq367295 eq367327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367295 eq367327
  have eq367758 : ∀ X0 X2 : G, (M.op X0 (M.op y (M.op x X2))) = (M.op X0 (M.op x (M.op y X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq367169 X0 x X2
       have i₂ := eq367198 x X2 x
       grind)
    | exact superpose eq367198 eq367169
    | exact resolve eq367169 eq367198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367169 eq367198
  have eq367805 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq367537 eq26
    | exact resolve eq26 eq367537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq369360 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x (σ (M.op x y)))) := by
    first
    | exact superpose eq367537 eq367597
    | exact resolve eq367597 eq367537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367537 eq367597
  have eq369515 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op x (M.op y (M.op X0 (M.op x (M.op y X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq367712 X0 X1 X2
       have i₂ := eq367758 X1 (M.op X0 (M.op x (M.op y X2)))
       grind)
    | exact superpose eq367758 eq367712
    | exact resolve eq367712 eq367758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367712 eq367758
  have eq384520 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op x (σ (M.op x y))) x)) := by
    first
    | exact superpose eq369360 eq446
    | exact resolve eq446 eq369360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq369360
  have eq384611 : (σ (M.op x y)) = (M.op (σ x) (M.op x (M.op y (M.op x (M.op x (M.op y (M.op x (σ (M.op x y))))))))) := by
    first
    | (have i₁ := eq384520
       have i₂ := eq369515 x sF2 (M.op x sF1)
       grind)
    | exact superpose eq369515 eq384520
    | exact resolve eq384520 eq369515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369515 eq384520
  have eq384667 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq384611
       have i₂ := eq67917 sF2 sF1 x y x
       grind)
    | exact superpose eq67917 eq384611
    | exact resolve eq384611 eq67917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67917 eq384611
  have eq384717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq367805 eq384667
    | exact resolve eq384667 eq367805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367805 eq384667
  have eq384761 : False := by grind
  exact eq384761

/-- `Equation2891`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxy_x_pxy_Equation2891 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2891 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2891.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq21 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq26 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  clear eq19
  have eq35 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | (have j0 := eq26 X0
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq757 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq761 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq757 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq757
    | (have j0 := eq757 X0
       grind)
    | exact resolve eq757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq797 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq761 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq761
    | exact resolve eq761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq829 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq797 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq797
    | (have j0 := eq797 X0
       grind)
    | exact resolve eq797 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq849 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq829 X0
       grind)
    | exact superpose eq829 eq10
    | (have j1 := eq829 X0
       grind)
    | exact resolve eq10 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq882 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq849 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq849
    | (have j0 := eq849 X0
       grind)
    | exact resolve eq849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq898 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq882 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq882 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq882 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq969 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq898 (σ X0)
       grind)
    | exact superpose eq898 eq15
    | exact resolve eq15 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq898 (τ X0)
       grind)
    | exact superpose eq898 eq36
    | exact resolve eq36 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq975 X0
       have i₂ := eq898 X0
       grind)
    | exact superpose eq898 eq975
    | exact resolve eq975 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1002 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq969 X0
       have i₂ := eq898 X0
       grind)
    | exact superpose eq898 eq969
    | exact resolve eq969 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq969
  have eq1034 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq35
    | (have j0 := eq35 X0
       grind)
    | exact resolve eq35 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1124 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = X0 ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1034 X0
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq1034
    | (have j0 := eq1034 X0
       grind)
    | exact resolve eq1034 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1169 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1124 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1124
    | (have j0 := eq1124 X0
       grind)
    | exact resolve eq1124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1195 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq9
    | exact resolve eq9 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1195 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq1195 X0 (M.op (τ (M.op X0 X0)) X0)
       have r₂ := eq12 X0 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq1195 X0 X1
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq1195 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1230 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq9
    | exact resolve eq9 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1236 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1230 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq1230 X0 (M.op (σ (M.op X0 X0)) X0)
       have r₂ := eq12 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq1230 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq1230 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1249 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (M.op X0 (M.op (τ X1) (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1198 X1 (M.op X0 (M.op (τ X1) (τ (M.op X1 X1))))
       have i₂ := eq9 X0 (τ X1) (τ (M.op X1 X1))
       grind)
    | exact superpose eq9 eq1198
    | exact resolve eq1198 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1280 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op X0 (M.op (σ X1) (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1233 X1 (M.op X0 (M.op (σ X1) (σ (M.op X1 X1))))
       have i₂ := eq9 X0 (σ X1) (σ (M.op X1 X1))
       grind)
    | exact superpose eq9 eq1233
    | exact resolve eq1233 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1322 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = (M.op X1 (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1249 X1 (σ X0)
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq1249
    | exact resolve eq1249 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1345 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = (M.op X1 (M.op (τ (σ X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1322 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1322
    | exact resolve eq1322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1351 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1345 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1345
    | exact resolve eq1345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1362 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X1 X1)
       have i₂ := eq1351 X1 X0
       grind)
    | exact superpose eq1351 eq9
    | exact resolve eq9 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1362 (M.op (M.op X0 (M.op X1 X2)) X2) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1362
    | exact resolve eq1362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1389 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1362 (M.op (M.op X0 X1) (M.op X1 X1)) X1
       have i₂ := eq1362 X0 X1
       grind)
    | exact superpose eq1362 eq1362
    | exact resolve eq1362 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1362 (σ X0) (σ X0)
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq1362
    | exact resolve eq1362 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1362 (τ X0) (τ X0)
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq1362
    | exact resolve eq1362 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1400 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1362 (M.op X0 (M.op (M.op X1 X1) X1)) X1
       have i₂ := eq9 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq9 eq1362
    | exact resolve eq1362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1406 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 X2) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X2) (M.op X2 X2)) X2
       have i₂ := eq1362 X0 X2
       grind)
    | exact superpose eq1362 eq9
    | exact resolve eq9 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1407 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) (M.op X1 X2))) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) (M.op X1 X2))) X1 X2
       have i₂ := eq1362 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1362 eq9
    | exact resolve eq9 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1424 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1393 X0
       have i₂ := eq996 (M.op X0 X0)
       grind)
    | exact superpose eq996 eq1393
    | exact resolve eq1393 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1425 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1392 X0
       have i₂ := eq1002 (M.op X0 X0)
       grind)
    | exact superpose eq1002 eq1392
    | exact resolve eq1392 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1433 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1362 X0 X1
       have i₂ := eq1389 (M.op X0 X1) X1
       grind)
    | exact superpose eq1389 eq1362
    | exact resolve eq1362 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1434 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X0 X1) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1388 X0 X1 X2
       have i₂ := eq1389 X0 X1
       grind)
    | exact superpose eq1389 eq1388
    | exact resolve eq1388 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq1389
  have eq1455 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1455_14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X1)) = X0 := by
      intro X0 X1
      grind
    have f1455_21 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
      intro X0 X1
      grind
    have f1455_24 : X1 ≠ (M.op (M.op X0 X1) X0) := by grind
    have f1455_25 : (M.op X1 X0) ≠ (k X1 X0) := by grind
    have f1455_26 : X0 ≠ (M.op X0 X1) := by grind
    have f1455_81 : (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = (M.op X1 X1) ∨ X0 = (M.op X0 X1) := by
      first
      | (have i₁ := f1455_25
         have i₂ := f1455_21 X1 X0
         grind)
      | exact superpose f1455_21 f1455_25
      | (have j1 := f1455_21 X1 X0
         grind)
      | (have r₁ := f1455_25
         have r₂ := f1455_21 X1 X0
         grind)
      | exact resolve f1455_25 f1455_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1455_89 : X0 = (M.op X1 X1) ∨ X0 = (M.op X0 X1) := by grind
    have f1455_96 : X0 = (M.op X1 X1) := by
      first
      | (have r₁ := f1455_89
         have r₂ := f1455_26
         grind)
      | exact resolve f1455_89 f1455_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1455_101 : X1 = (M.op (M.op X0 X1) X0) := by
      first
      | (have i₁ := f1455_14 X1 X1
         have i₂ := f1455_96
         grind)
      | exact superpose f1455_96 f1455_14
      | exact resolve f1455_14 f1455_96
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1455_105 : False := by
      first
      | (have r₁ := f1455_101
         have r₂ := f1455_24
         grind)
      | exact resolve f1455_101 f1455_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1455_105
  have eq1463 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1433 (τ X0) (τ X0)
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq1433
    | exact resolve eq1433 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1472 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) (σ X0)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1433 X1 (σ X0)
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq1433
    | exact resolve eq1433 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1473 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ X0)) (τ X0)) (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1433 X1 (τ X0)
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq1433
    | exact resolve eq1433 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1485 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1455 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1455 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1455 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq1566 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X1)) X1) (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1433 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq1400 (M.op X0 (M.op (M.op X1 X1) X1)) X1
       grind)
    | exact superpose eq1400 eq1433
    | exact resolve eq1433 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1569 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X1)) X1) (M.op (M.op (M.op X1 X1) X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1566 X0 X1
       have i₂ := eq1400 (M.op (M.op X1 X1) X1) X1
       grind)
    | exact superpose eq1400 eq1566
    | exact resolve eq1566 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1586 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X1 X1) X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1569 X0 X1
       have i₂ := eq1400 X0 X1
       grind)
    | exact superpose eq1400 eq1569
    | exact resolve eq1569 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1775 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op (M.op X0 X0) X0) X0))) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq1425 (M.op (M.op x x) x)
       have i₂ := eq1400 (M.op (M.op x x) x) x
       grind)
    | exact superpose eq1400 eq1425
    | exact resolve eq1425 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1805 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq1775 X0
       have i₂ := eq1586 (M.op X0 X0) X0
       grind)
    | exact superpose eq1586 eq1775
    | exact resolve eq1775 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586 eq1775
  have eq2166 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1473 X0 (τ (M.op X0 X0))
       have i₂ := eq1169 X0
       grind)
    | exact superpose eq1169 eq1473
    | (have j1 := eq1169 X0
       grind)
    | exact resolve eq1473 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2178 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2166 X0
       have i₂ := eq1463 X0
       grind)
    | exact superpose eq1463 eq2166
    | (have j0 := eq2166 X0
       grind)
    | exact resolve eq2166 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq2166
  have eq2313 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq2178 (σ X0)
       grind)
    | exact superpose eq2178 eq22
    | (have j1 := eq2178 (σ X0)
       grind)
    | exact resolve eq22 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2178
  have eq2330 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2313 X0
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq2313
    | (have j0 := eq2313 X0
       grind)
    | exact resolve eq2313 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313
  have eq2349 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2330 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2330
    | (have j0 := eq2330 X0
       grind)
    | exact resolve eq2330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq2366 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2349 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2349
    | (have j0 := eq2349 X0
       grind)
    | exact resolve eq2349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2382 : ∀ X0 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2366 X0
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq2366
    | (have j0 := eq2366 X0
       grind)
    | exact resolve eq2366 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2394 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2382 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2382
    | (have j0 := eq2382 X0
       grind)
    | exact resolve eq2382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq2401 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2394 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2394
    | (have j0 := eq2394 X0
       grind)
    | exact resolve eq2394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2417 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2401 (σ X0)
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq2401
    | exact resolve eq2401 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2446 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2417 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq2417
    | (have j0 := eq2417 X0
       grind)
    | exact resolve eq2417 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq2828 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1202 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1202
    | (have j0 := eq1202 (σ X0) X1
       grind)
    | exact resolve eq1202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq2909 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2828 X0 X1
       have i₂ := eq1002 X0
       grind)
    | exact superpose eq1002 eq2828
    | (have j0 := eq2828 X0 X1
       grind)
    | exact resolve eq2828 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828
  have eq2915 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2909 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2909
    | (have j0 := eq2909 X0 X1
       grind)
    | exact resolve eq2909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2941 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq3043 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2941 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq2941 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2941 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941
  have eq3114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3043 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq3285 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1236 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1236 X0 (σ X0)
       grind)
    | exact superpose eq1236 eq10
    | (have j1 := eq1236 X1 X0
       grind)
    | exact resolve eq10 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq4004 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3285 (σ X1) X0
       grind)
    | exact superpose eq3285 eq15
    | (have j1 := eq3285 (σ X1) X0
       grind)
    | exact resolve eq15 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq4049 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4004 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4004
    | (have j0 := eq4004 X0 X1
       grind)
    | exact resolve eq4004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004
  have eq5362 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4049 x y
       grind)
    | exact superpose eq4049 eq16
    | (have j1 := eq4049 x y
       grind)
    | exact resolve eq16 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5542 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5362
       have i₂ := eq2915 x y
       grind)
    | exact superpose eq2915 eq5362
    | (have j1 := eq2915 x y
       grind)
    | exact resolve eq5362 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5362
  have eq5549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq5542
  have eq5550 : y = (M.op x x) := by grind
  clear eq5549
  have eq5566 : (τ y) = (M.op (τ y) (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1169 x
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq1169
    | exact resolve eq1169 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq5571 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1351 x X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq1351
    | exact resolve eq1351 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq5572 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq1400 X0 x
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq1400
    | exact resolve eq1400 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5574 : (σ x) = (M.op (σ (M.op y y)) (σ x)) := by
    first
    | (have i₁ := eq1425 x
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq1425
    | exact resolve eq1425 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5575 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1433 X0 x
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq1433
    | exact resolve eq1433 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5578 : ∀ X0 : G, (M.op (M.op (M.op X0 (τ x)) (τ x)) (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1473 x X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq1473
    | exact resolve eq1473 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq5594 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq9
    | exact resolve eq9 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5653 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) (σ (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1472 (M.op x y) X0
       have i₂ := eq5571 (M.op x y)
       grind)
    | exact superpose eq5571 eq1472
    | exact resolve eq1472 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq5671 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op x y) X0
       have i₂ := eq5571 X0
       grind)
    | exact superpose eq5571 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5679 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) X1) x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op x y) X1
       have i₂ := eq5571 (M.op (M.op X0 (M.op (M.op x y) X1)) X1)
       grind)
    | exact superpose eq5571 eq9
    | exact resolve eq9 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5762 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y x) X1)) X1) x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op y x) X1
       have i₂ := eq5572 (M.op (M.op X0 (M.op (M.op y x) X1)) X1)
       grind)
    | exact superpose eq5572 eq9
    | exact resolve eq9 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq5795 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq5575 x
       have i₂ := eq2915 x X0
       grind)
    | (have i₁ := eq5575 X0
       have i₂ := eq2915 X0 (M.op X0 x)
       grind)
    | exact superpose eq2915 eq5575
    | (have j1 := eq2915 x X0
       grind)
    | exact resolve eq5575 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5807 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) y) (M.op (M.op X0 x) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 x) x) y
       have i₂ := eq5575 X0
       grind)
    | exact superpose eq5575 eq9
    | exact resolve eq9 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5809 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 y) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq1433 (M.op (M.op X0 x) x) y
       have i₂ := eq5575 X0
       grind)
    | exact superpose eq5575 eq1433
    | exact resolve eq1433 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5837 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq5575 (M.op (M.op X0 y) x)
       have i₂ := eq5594 X0
       grind)
    | exact superpose eq5594 eq5575
    | exact resolve eq5575 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5838 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) x) (M.op (M.op X0 y) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 y) x) x
       have i₂ := eq5594 X0
       grind)
    | exact superpose eq5594 eq9
    | exact resolve eq9 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5594
  have eq5849 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) x) (M.op (M.op X0 x) y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5838 X0 X1
       have i₂ := eq5837 X0
       grind)
    | exact superpose eq5837 eq5838
    | exact resolve eq5838 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838
  have eq5862 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) (σ (M.op (M.op x x) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5653 X0
       have i₂ := eq5837 x
       grind)
    | exact superpose eq5837 eq5653
    | exact resolve eq5653 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5653
  have eq5908 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5862 X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq5862
    | exact resolve eq5862 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5862
  have eq6995 : (τ x) = (M.op (M.op (τ (M.op x x)) (τ x)) (τ y)) := by
    first
    | (have i₁ := eq5578 (τ x)
       have i₂ := eq996 x
       grind)
    | exact superpose eq996 eq5578
    | exact resolve eq5578 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5578
  have eq7017 : (τ x) = (M.op (M.op (τ y) (τ x)) (τ y)) := by
    first
    | (have i₁ := eq6995
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq6995
    | exact resolve eq6995 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6995
  have eq8128 : (τ x) = (M.op (τ y) (τ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq7017
       have i₂ := eq5566
       grind)
    | exact superpose eq5566 eq7017
    | exact resolve eq7017 eq5566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5566
  have eq8158 : (τ x) = (τ (M.op y y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8128
       have i₂ := eq996 y
       grind)
    | exact superpose eq996 eq8128
    | exact resolve eq8128 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996 eq8128
  have eq8300 : (τ x) = (M.op (τ (M.op (M.op (M.op y y) (M.op y y)) (M.op (M.op y y) (M.op y y)))) (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1424 (M.op y y)
       have i₂ := eq8158
       grind)
    | exact superpose eq8158 eq1424
    | exact resolve eq1424 eq8158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq8158
  have eq8316 : (τ x) = (M.op (τ (M.op (M.op (M.op y y) y) y)) (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8300
       have i₂ := eq1407 (M.op y y) y y
       grind)
    | exact superpose eq1407 eq8300
    | exact resolve eq8300 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8300
  have eq9325 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq1433 (M.op X0 (M.op (M.op x y) x)) x
       have i₂ := eq5679 X0 x
       grind)
    | exact superpose eq5679 eq1433
    | exact resolve eq1433 eq5679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9326 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op x y) (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op x y) (M.op X1 x))) X1 x
       have i₂ := eq5679 X0 (M.op X1 x)
       grind)
    | exact superpose eq5679 eq9
    | exact resolve eq9 eq5679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679
  have eq9346 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op (M.op x x) y)) := by
    intro X0
    first
    | (have i₁ := eq9325 X0
       have i₂ := eq5837 x
       grind)
    | exact superpose eq5837 eq9325
    | exact resolve eq9325 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325
  have eq9395 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9346 X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq9346
    | exact resolve eq9346 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9346
  have eq9434 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq5809 X0
       have i₂ := eq9395 (M.op X0 y)
       grind)
    | exact superpose eq9395 eq5809
    | exact resolve eq5809 eq9395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5809
  have eq9525 : (τ x) = (M.op (τ (M.op (M.op (M.op y y) x) x)) (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8316
       have i₂ := eq9434 (M.op y y)
       grind)
    | exact superpose eq9434 eq8316
    | exact resolve eq8316 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8316
  have eq9535 : (τ x) = (M.op (τ (M.op (M.op (M.op y x) y) x)) (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9525
       have i₂ := eq5837 y
       grind)
    | exact superpose eq5837 eq9525
    | exact resolve eq9525 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9525
  have eq9538 : (τ x) = (M.op (τ (M.op (M.op (M.op y x) x) y)) (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9535
       have i₂ := eq5837 (M.op y x)
       grind)
    | exact superpose eq5837 eq9535
    | exact resolve eq9535 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9535
  have eq9539 : (τ x) = (M.op (τ y) (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9538
       have i₂ := eq5575 y
       grind)
    | exact superpose eq5575 eq9538
    | exact resolve eq9538 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9538
  have eq9576 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op X0 (M.op (σ (M.op y y)) (σ (M.op (M.op y y) y)))) := by
    intro X0
    first
    | (have i₁ := eq1280 X0 (M.op y y)
       have i₂ := eq9395 (M.op y y)
       grind)
    | exact superpose eq9395 eq1280
    | exact resolve eq1280 eq9395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9608 : (σ y) = (M.op (σ (M.op (M.op y y) y)) (σ y)) := by
    first
    | (have i₁ := eq1425 y
       have i₂ := eq9395 (M.op y y)
       grind)
    | exact superpose eq9395 eq1425
    | exact resolve eq1425 eq9395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq9622 : (σ y) = (M.op (σ (M.op (M.op y x) x)) (σ y)) := by
    first
    | (have i₁ := eq9608
       have i₂ := eq9434 y
       grind)
    | exact superpose eq9434 eq9608
    | exact resolve eq9608 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9608
  have eq9651 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op X0 (σ (M.op (M.op y y) y))) := by
    intro X0
    first
    | (have i₁ := eq9576 X0
       have i₂ := eq1805 y
       grind)
    | exact superpose eq1805 eq9576
    | exact resolve eq9576 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805 eq9576
  have eq9691 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op X0 (σ (M.op (M.op y x) x))) := by
    intro X0
    first
    | (have i₁ := eq9651 X0
       have i₂ := eq9434 y
       grind)
    | exact superpose eq9434 eq9651
    | exact resolve eq9651 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9651
  have eq9749 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) x)) := by
    intro X0
    first
    | (have i₁ := eq1400 X0 y
       have i₂ := eq9434 y
       grind)
    | exact superpose eq9434 eq1400
    | exact resolve eq1400 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq9838 : ∀ X0 : G, (M.op X0 (σ (M.op (M.op y x) x))) = (M.op X0 (M.op (σ (M.op (M.op y x) x)) (σ (M.op (M.op (M.op y x) x) y)))) := by
    intro X0
    first
    | (have i₁ := eq1280 X0 (M.op (M.op y x) x)
       have i₂ := eq9749 (M.op (M.op y x) x)
       grind)
    | exact superpose eq9749 eq1280
    | exact resolve eq1280 eq9749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq9749
  have eq9907 : ∀ X0 : G, (M.op X0 (σ (M.op (M.op y x) x))) = (M.op X0 (M.op (σ (M.op (M.op y x) x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq9838 X0
       have i₂ := eq5575 y
       grind)
    | exact superpose eq5575 eq9838
    | exact resolve eq9838 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9838
  have eq9950 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op y x) x))) := by
    intro X0
    first
    | (have i₁ := eq9907 X0
       have i₂ := eq9622
       grind)
    | exact superpose eq9622 eq9907
    | exact resolve eq9907 eq9622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9622 eq9907
  have eq9975 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq9950 X0
       have i₂ := eq9691 X0
       grind)
    | exact superpose eq9691 eq9950
    | exact resolve eq9950 eq9691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9691 eq9950
  have eq9993 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5908 X0
       have i₂ := eq9975 (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y)))
       grind)
    | exact superpose eq9975 eq5908
    | exact resolve eq5908 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5908
  have eq10110 : ∀ X0 : G, (M.op X0 (σ y)) ≠ X0 ∨ (k X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3114 X0 (σ (M.op y y))
       have i₂ := eq9975 X0
       grind)
    | exact superpose eq9975 eq3114
    | (have j0 := eq3114 X0 (σ y)
       grind)
    | exact resolve eq3114 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11270 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op (M.op y x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5762 (M.op X0 (M.op X1 (M.op (M.op y x) X1))) X1
       have i₂ := eq9 X0 X1 (M.op (M.op y x) X1)
       grind)
    | exact superpose eq9 eq5762
    | exact resolve eq5762 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11292 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y x) (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op y x) (M.op X1 x))) X1 x
       have i₂ := eq5762 X0 (M.op X1 x)
       grind)
    | exact superpose eq5762 eq9
    | exact resolve eq9 eq5762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5762
  have eq11485 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X0 y) (M.op (M.op X1 x) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5807 X1 (M.op (M.op X0 (M.op X1 X2)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq5807
    | exact resolve eq5807 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11487 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) (M.op (M.op (M.op (M.op X1 x) x) x) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq5807 (M.op (M.op X1 x) x) (M.op (M.op X0 X1) y)
       have i₂ := eq5807 X1 X0
       grind)
    | exact superpose eq5807 eq5807
    | exact resolve eq5807 eq5807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11520 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 (M.op (M.op X1 x) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq5807 X1 (M.op X0 (M.op y X1))
       have i₂ := eq9 X0 y X1
       grind)
    | exact superpose eq9 eq5807
    | exact resolve eq5807 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11548 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 x) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) y) (M.op X1 x) x
       have i₂ := eq5807 X1 X0
       grind)
    | exact superpose eq5807 eq9
    | exact resolve eq9 eq5807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5807
  have eq11559 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq11292 X0 X1
       have i₂ := eq11548 y X1
       grind)
    | exact superpose eq11548 eq11292
    | exact resolve eq11292 eq11548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11292
  have eq11610 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) (M.op y (M.op (M.op X1 x) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq11487 X0 X1
       have i₂ := eq11520 (M.op X0 y) (M.op (M.op X1 x) x)
       grind)
    | exact superpose eq11520 eq11487
    | exact resolve eq11487 eq11520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11487
  have eq11612 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X0 y) (M.op y X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11485 X0 X1 X2
       have i₂ := eq11520 (M.op X0 y) X1
       grind)
    | exact superpose eq11520 eq11485
    | exact resolve eq11485 eq11520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11485
  have eq11665 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) (M.op y (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11610 X0 X1
       have i₂ := eq11520 y X1
       grind)
    | exact superpose eq11520 eq11610
    | exact resolve eq11610 eq11520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11610
  have eq11677 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op (M.op X0 y) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1434 X0 X1 x
       have i₂ := eq11612 X0 X1 x
       grind)
    | exact superpose eq11612 eq1434
    | exact resolve eq1434 eq11612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq12258 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 (M.op (M.op X1 x) y)) (M.op (M.op (M.op X1 x) y) (M.op (M.op X1 x) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1433 (M.op (M.op X0 X1) x) (M.op (M.op X1 x) y)
       have i₂ := eq5849 X1 X0
       grind)
    | exact superpose eq5849 eq1433
    | exact resolve eq1433 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12264 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 y) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq12258 X0 X1
       have i₂ := eq1407 X0 (M.op X1 x) y
       grind)
    | exact superpose eq1407 eq12258
    | exact resolve eq12258 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12258
  have eq12304 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op x X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq9326 X0 X1
       have i₂ := eq12264 x X1
       grind)
    | exact superpose eq12264 eq9326
    | exact resolve eq9326 eq12264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9326
  have eq12419 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op (M.op (M.op (M.op x X1) x) x) y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5849 (M.op (M.op x X1) x) X0
       have i₂ := eq12304 X0 X1
       grind)
    | exact superpose eq12304 eq5849
    | exact resolve eq5849 eq12304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12304
  have eq12434 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12419 X0 X1
       have i₂ := eq5575 (M.op x X1)
       grind)
    | exact superpose eq5575 eq12419
    | exact resolve eq12419 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12419
  have eq12503 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 x) (M.op x (M.op x X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12434 (M.op (M.op X0 X1) x) (M.op x X1)
       have i₂ := eq12434 X0 X1
       grind)
    | exact superpose eq12434 eq12434
    | exact resolve eq12434 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13188 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op X0 y))) = (M.op X1 (M.op (M.op (M.op X0 x) y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq11520 X1 (M.op X0 y)
       have i₂ := eq5837 X0
       grind)
    | exact superpose eq5837 eq11520
    | exact resolve eq11520 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13292 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X0 x) x) y)) = (M.op X1 (M.op y (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq13188 X0 X1
       have i₂ := eq5837 (M.op X0 x)
       grind)
    | exact superpose eq5837 eq13188
    | exact resolve eq13188 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13188
  have eq13315 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq13292 X0 X1
       have i₂ := eq5575 X0
       grind)
    | exact superpose eq5575 eq13292
    | exact resolve eq13292 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13292
  have eq13347 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op y (M.op (M.op X0 x) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq13315 (M.op X0 y) X1
       have i₂ := eq9434 X0
       grind)
    | exact superpose eq9434 eq13315
    | exact resolve eq13315 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13450 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op y (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13347 X0 X1
       have i₂ := eq11520 y X0
       grind)
    | exact superpose eq11520 eq13347
    | exact resolve eq13347 eq11520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13347
  have eq13463 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq11665 X0 X1
       have i₂ := eq13450 X1 (M.op X0 y)
       grind)
    | exact superpose eq13450 eq11665
    | exact resolve eq11665 eq13450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11665
  have eq13492 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq11548 x X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq11548
    | exact resolve eq11548 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13503 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 y)) y) = (M.op (M.op X1 x) (M.op (M.op X0 x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq11548 X1 (M.op X0 y)
       have i₂ := eq5837 X0
       grind)
    | exact superpose eq5837 eq11548
    | exact resolve eq11548 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13530 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op (M.op X0 x) (M.op (M.op y X0) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq11270 X1 (M.op X0 x)
       have i₂ := eq11548 y X0
       grind)
    | exact superpose eq11548 eq11270
    | exact resolve eq11270 eq11548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11270
  have eq13575 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) y) x) (M.op (M.op (M.op X1 x) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq5849 (M.op X1 x) (M.op X0 x)
       have i₂ := eq11548 X0 X1
       grind)
    | exact superpose eq11548 eq5849
    | exact resolve eq5849 eq11548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849
  have eq13580 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) y) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13575 X0 X1
       have i₂ := eq5575 X1
       grind)
    | exact superpose eq5575 eq13575
    | exact resolve eq13575 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13575
  have eq13595 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op (M.op X0 x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13530 X0 X1
       have i₂ := eq11559 (M.op X0 x) X0
       grind)
    | exact superpose eq11559 eq13530
    | exact resolve eq13530 eq11559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13530
  have eq13599 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op y X0)) = (M.op (M.op X1 x) (M.op (M.op X0 x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13503 X0 X1
       have i₂ := eq11612 X1 X0 y
       grind)
    | exact superpose eq11612 eq13503
    | exact resolve eq13503 eq11612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13503
  have eq13614 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) x) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13580 X0 X1
       have i₂ := eq5837 (M.op X0 X1)
       grind)
    | exact superpose eq5837 eq13580
    | exact resolve eq13580 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13580
  have eq13958 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op y (M.op y (M.op X0 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13315 (M.op x X0) X1
       have i₂ := eq13492 X0
       grind)
    | exact superpose eq13492 eq13315
    | exact resolve eq13315 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13315
  have eq13977 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op (M.op X0 x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13958 X0 X1
       have i₂ := eq13450 (M.op X0 x) X1
       grind)
    | exact superpose eq13450 eq13958
    | exact resolve eq13958 eq13450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13450 eq13958
  have eq14012 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op y X0)) = (M.op (M.op X1 x) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13599 X0 X1
       have i₂ := eq13977 X0 (M.op X1 x)
       grind)
    | exact superpose eq13977 eq13599
    | exact resolve eq13599 eq13977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13599
  have eq14028 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X0 x) (M.op x X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11612 X0 X1 X2
       have i₂ := eq14012 X1 X0
       grind)
    | exact superpose eq14012 eq11612
    | exact resolve eq11612 eq14012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11612
  have eq14035 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op (M.op X0 x) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11677 X0 X1
       have i₂ := eq14012 X1 X0
       grind)
    | exact superpose eq14012 eq11677
    | exact resolve eq11677 eq14012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11677 eq14012
  have eq14202 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) (M.op (M.op X1 x) X1)) (M.op (M.op (M.op X1 x) X1) (M.op (M.op X1 x) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1433 X0 (M.op (M.op X1 x) X1)
       have i₂ := eq13595 X1 X0
       grind)
    | exact superpose eq13595 eq1433
    | exact resolve eq1433 eq13595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13595
  have eq14232 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op X1 x)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14202 X0 X1
       have i₂ := eq1407 (M.op X0 x) (M.op X1 x) X1
       grind)
    | exact superpose eq1407 eq14202
    | exact resolve eq14202 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14202
  have eq14483 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14232 x X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq14232
    | exact resolve eq14232 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14232
  have eq14661 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 y)) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq14483 (M.op X0 y)
       have i₂ := eq5837 X0
       grind)
    | exact superpose eq5837 eq14483
    | exact resolve eq14483 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14483
  have eq14706 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14661 X0
       have i₂ := eq13977 X0 (M.op y (M.op X0 y))
       grind)
    | exact superpose eq13977 eq14661
    | exact resolve eq14661 eq13977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14661
  have eq14984 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x x) (M.op x (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq12434 (M.op y (M.op X0 y)) (M.op x X0)
       have i₂ := eq14706 X0
       grind)
    | exact superpose eq14706 eq12434
    | exact resolve eq12434 eq14706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12434 eq14706
  have eq14985 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq14984 X0
       have i₂ := eq12503 x X0
       grind)
    | exact superpose eq12503 eq14984
    | exact resolve eq14984 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503 eq14984
  have eq15229 : ∀ X0 : G, (M.op (M.op x (M.op y X0)) x) = (M.op y (M.op (M.op (M.op X0 x) x) y)) := by
    intro X0
    first
    | (have i₁ := eq14985 (M.op (M.op X0 x) x)
       have i₂ := eq11520 x X0
       grind)
    | exact superpose eq11520 eq14985
    | exact resolve eq14985 eq11520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520
  have eq15307 : ∀ X0 : G, (M.op (M.op x (M.op y X0)) x) = (M.op y (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq15229 X0
       have i₂ := eq13977 (M.op X0 x) y
       grind)
    | exact superpose eq13977 eq15229
    | exact resolve eq15229 eq13977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15229
  have eq15347 : ∀ X0 : G, (M.op y (M.op (M.op y X0) y)) = (M.op y (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq15307 X0
       have i₂ := eq14985 (M.op y X0)
       grind)
    | exact superpose eq14985 eq15307
    | exact resolve eq15307 eq14985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14985 eq15307
  have eq15356 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq15347 X0
       have i₂ := eq11559 y X0
       grind)
    | exact superpose eq11559 eq15347
    | exact resolve eq15347 eq11559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15347
  have eq15383 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X0) y)) = (M.op X1 (M.op x (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq11559 X1 (M.op x (M.op X0 x))
       have i₂ := eq15356 X0
       grind)
    | exact superpose eq15356 eq11559
    | exact resolve eq11559 eq15356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15356
  have eq15397 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op x (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq15383 X0 X1
       have i₂ := eq11559 X1 X0
       grind)
    | exact superpose eq11559 eq15383
    | exact resolve eq15383 eq11559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11559 eq15383
  have eq15633 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) x) = (M.op (M.op (M.op X0 x) x) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq12264 (M.op X0 y) X1
       have i₂ := eq9434 X0
       grind)
    | exact superpose eq9434 eq12264
    | exact resolve eq12264 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq15636 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op (M.op (M.op X0 x) x) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq12264 (M.op (M.op X0 x) x) X1
       have i₂ := eq5575 X0
       grind)
    | exact superpose eq5575 eq12264
    | exact resolve eq12264 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15705 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) x) = (M.op (M.op (M.op X0 x) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq15633 X0 X1
       have i₂ := eq11548 (M.op X0 x) X1
       grind)
    | exact superpose eq11548 eq15633
    | exact resolve eq15633 eq11548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15633
  have eq15967 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 x) x) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq13463 (M.op (M.op X0 x) x) X1
       have i₂ := eq5575 X0
       grind)
    | exact superpose eq5575 eq13463
    | exact resolve eq13463 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16162 : (τ x) = (M.op (τ x) (τ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq7017
       have i₂ := eq9539
       grind)
    | exact superpose eq9539 eq7017
    | exact resolve eq7017 eq9539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017 eq9539
  have eq17951 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op (M.op (M.op (M.op X0 X1) y) x) y) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13614 (M.op X0 x) (M.op X1 x)
       have i₂ := eq11548 X0 X1
       grind)
    | exact superpose eq11548 eq13614
    | exact resolve eq13614 eq11548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11548
  have eq17952 : ∀ X0 X1 : G, (M.op (M.op X0 y) x) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) y) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13614 (M.op X0 y) (M.op X1 x)
       have i₂ := eq12264 X0 X1
       grind)
    | exact superpose eq12264 eq13614
    | exact resolve eq13614 eq12264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13614
  have eq18182 : ∀ X0 X1 : G, (M.op (M.op X0 y) x) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq17952 X0 X1
       have i₂ := eq12264 (M.op (M.op (M.op X0 X1) x) x) X1
       grind)
    | exact superpose eq12264 eq17952
    | exact resolve eq17952 eq12264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17952
  have eq18183 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op (M.op (M.op (M.op X0 X1) y) x) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq17951 X0 X1
       have i₂ := eq12264 (M.op (M.op (M.op X0 X1) y) x) X1
       grind)
    | exact superpose eq12264 eq17951
    | exact resolve eq17951 eq12264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17951
  have eq18261 : ∀ X0 X1 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 X1) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq18182 X0 X1
       have i₂ := eq15636 (M.op X0 X1) X1
       grind)
    | exact superpose eq15636 eq18182
    | exact resolve eq18182 eq15636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15636 eq18182
  have eq18262 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) y) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq18183 X0 X1
       have i₂ := eq5837 (M.op X0 X1)
       grind)
    | exact superpose eq5837 eq18183
    | exact resolve eq18183 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18183
  have eq18301 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 X1) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq18261 X0 X1
       have i₂ := eq5837 X0
       grind)
    | exact superpose eq5837 eq18261
    | exact resolve eq18261 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18261
  have eq18302 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq18262 X0 X1
       have i₂ := eq15705 (M.op (M.op X0 X1) x) X1
       grind)
    | exact superpose eq15705 eq18262
    | exact resolve eq18262 eq15705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18262
  have eq18369 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18302 X0 X1
       have i₂ := eq15967 (M.op X0 X1) X1
       grind)
    | exact superpose eq15967 eq18302
    | exact resolve eq18302 eq15967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15967 eq18302
  have eq21286 : (τ x) ≠ (τ x) ∨ (τ x) = (k (τ x) (τ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3114 (τ x) (τ y)
       have i₂ := eq16162
       grind)
    | exact superpose eq16162 eq3114
    | (have j0 := eq3114 (τ x) (τ y)
       grind)
    | (have r₁ := eq3114 (τ x) (τ y)
       have r₂ := eq16162
       grind)
    | exact resolve eq3114 eq16162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114 eq16162
  have eq21294 : (τ x) = (k (τ x) (τ y)) ∨ x = (k x y) := by grind
  clear eq21286
  have eq21301 : (τ x) = (τ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq21294
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq21294
    | exact resolve eq21294 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq21294
  have eq21561 : (k x y) = (σ (τ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq21301
       grind)
    | exact superpose eq21301 eq11
    | exact resolve eq11 eq21301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21301
  have eq21630 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq21561
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq21561
    | exact resolve eq21561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21561
  have eq21631 : x = (k x y) := by grind
  clear eq21630
  have eq26308 : ∀ X0 : G, (M.op x (M.op X0 x)) = (k x (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq5575 X0
       have i₂ := eq5795 (M.op X0 x)
       grind)
    | exact superpose eq5795 eq5575
    | (have j1 := eq5795 (M.op X0 x)
       grind)
    | exact resolve eq5575 eq5795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5795
  have eq29048 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x X0) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq26308 (M.op x x)
       have i₂ := eq1485 x x
       grind)
    | exact superpose eq1485 eq26308
    | (have j0 := eq26308 (M.op x X0)
       have j1 := eq1485 X0 x
       grind)
    | exact resolve eq26308 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485 eq26308
  have eq29062 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq29048 X0
       have j1 := eq12 x X0
       grind)
    | (have r₁ := eq29048 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq29048 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29048
  have eq30431 : x = (M.op x y) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq21631
       have i₂ := eq29062 y
       grind)
    | exact superpose eq29062 eq21631
    | (have j1 := eq29062 y
       grind)
    | exact resolve eq21631 eq29062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21631 eq29062
  have eq30485 : (M.op y x) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq30431
       have r₂ := eq12 y x
       grind)
    | exact resolve eq30431 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30431
  have eq30681 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq10110 (σ y)
       have i₂ := eq1002 y
       grind)
    | exact superpose eq1002 eq10110
    | (have j0 := eq10110 (σ y)
       grind)
    | exact resolve eq10110 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10110
  have eq30689 : (σ y) = (σ (k y (M.op y y))) ∨ (σ y) ≠ (σ (M.op y y)) := by
    first
    | (have i₁ := eq30681
       have i₂ := eq15 y (M.op y y)
       grind)
    | exact superpose eq15 eq30681
    | exact resolve eq30681 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30681
  have eq30704 : (σ y) = (σ (k y (M.op y y))) := by
    first
    | (have j1 := eq2446 y
       grind)
    | (have r₁ := eq30689
       have r₂ := eq2446 y
       grind)
    | exact resolve eq30689 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446 eq30689
  have eq30734 : (τ (σ y)) = (k y (M.op y y)) := by
    first
    | (have i₁ := eq10 (k y (M.op y y))
       have i₂ := eq30704
       grind)
    | exact superpose eq30704 eq10
    | exact resolve eq10 eq30704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30704
  have eq30786 : y = (k y (M.op y y)) := by
    first
    | (have i₁ := eq30734
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq30734
    | exact resolve eq30734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30734
  have eq42996 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 (M.op (M.op X1 X2) (M.op X2 X2))) (M.op (M.op (M.op X1 X2) (M.op X2 X2)) (M.op (M.op X1 X2) (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1406 X2 (M.op X0 X1) (M.op (M.op X1 X2) (M.op X2 X2))
       have i₂ := eq1406 X1 X0 X2
       grind)
    | exact superpose eq1406 eq1406
    | exact resolve eq1406 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43148 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X2)) (M.op X2 X2)) (M.op X0 (M.op (M.op X2 X2) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1406 (M.op (M.op X0 X2) X2) X1 (M.op X2 X2)
       have i₂ := eq1433 X0 X2
       grind)
    | exact superpose eq1433 eq1406
    | exact resolve eq1406 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43333 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 X2))) (M.op (M.op (M.op X1 X2) (M.op X2 X2)) (M.op (M.op X1 X2) (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1433 (M.op (M.op X0 X1) X2) (M.op (M.op X1 X2) (M.op X2 X2))
       have i₂ := eq1406 X1 X0 X2
       grind)
    | exact superpose eq1406 eq1433
    | exact resolve eq1433 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43350 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43333 X0 X1 X2
       have i₂ := eq1407 X0 (M.op X1 X2) (M.op X2 X2)
       grind)
    | exact superpose eq1407 eq43333
    | exact resolve eq43333 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43333
  have eq43612 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 (M.op X2 X2)) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42996 X0 X1 X2
       have i₂ := eq1407 X2 (M.op X1 X2) (M.op X2 X2)
       grind)
    | exact superpose eq1407 eq42996
    | exact resolve eq42996 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42996
  have eq43919 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43612 X0 X1 X2
       have i₂ := eq43350 X2 X1 X2
       grind)
    | exact superpose eq43350 eq43612
    | exact resolve eq43612 eq43350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43612
  have eq44383 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) (M.op X3 X3))) = (M.op X1 (M.op X0 (M.op (M.op X0 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43919 X1 (M.op (M.op X2 X3) (M.op X3 X3)) (M.op (M.op X0 X2) X3)
       have i₂ := eq1406 X2 X0 X3
       grind)
    | exact superpose eq1406 eq43919
    | exact resolve eq43919 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq44575 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X1) X2)) (M.op (M.op (M.op X2 X1) X2) (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1433 X0 (M.op (M.op X2 X1) X2)
       have i₂ := eq43919 X0 X1 X2
       grind)
    | exact superpose eq43919 eq1433
    | exact resolve eq1433 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq44689 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44575 X0 X1 X2
       have i₂ := eq1407 (M.op X0 X1) (M.op X2 X1) X2
       grind)
    | exact superpose eq1407 eq44575
    | exact resolve eq44575 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq44575
  have eq44856 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44689 X1 X1 X2
       have i₂ := eq2915 X1 X0
       grind)
    | (have i₁ := eq44689 X0 X1 X2
       have i₂ := eq2915 X0 (M.op X0 X1)
       grind)
    | exact superpose eq2915 eq44689
    | (have j1 := eq2915 X1 X0
       grind)
    | exact resolve eq44689 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq44922 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op X3 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44689 (M.op (M.op X0 X1) X2) (M.op X2 X1) X3
       have i₂ := eq44689 X0 X1 X2
       grind)
    | exact superpose eq44689 eq44689
    | exact resolve eq44689 eq44689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45286 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op X0 (M.op (M.op X0 X3) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43919 X1 (M.op X2 X3) (M.op (M.op X0 X3) X2)
       have i₂ := eq44689 X0 X3 X2
       grind)
    | exact superpose eq44689 eq43919
    | exact resolve eq43919 eq44689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45287 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) (M.op X3 X3))) = (M.op X1 (M.op X3 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq44383 x X1 X2 X3
       have i₂ := eq45286 x X1 X3 X2
       grind)
    | exact superpose eq45286 eq44383
    | exact resolve eq44383 eq45286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44383 eq45286
  have eq45604 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X2)) (M.op X2 X2)) (M.op X0 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43148 X0 X1 X2
       have i₂ := eq45287 X0 X2 X2
       grind)
    | exact superpose eq45287 eq43148
    | exact resolve eq43148 eq45287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43148 eq45287
  have eq50395 : ∀ X0 X1 X2 : G, (M.op (M.op X2 x) (M.op x (M.op (M.op X0 X1) X0))) = (M.op (M.op X2 (M.op (M.op X0 X1) X0)) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14035 X2 (M.op (M.op X0 X1) X0)
       have i₂ := eq43919 (M.op (M.op X0 X1) X0) X1 X0
       grind)
    | exact superpose eq43919 eq14035
    | exact resolve eq14035 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50501 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14035 x X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq14035
    | exact resolve eq14035 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50747 : ∀ X0 X1 X2 : G, (M.op (M.op X2 x) (M.op x (M.op (M.op X0 X1) X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50395 X0 X1 X2
       have i₂ := eq43919 X2 X1 X0
       grind)
    | exact superpose eq43919 eq50395
    | exact resolve eq50395 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50395
  have eq50951 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50747 X0 X1 X2
       have i₂ := eq44922 X2 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq44922 eq50747
    | exact resolve eq50747 eq44922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50747
  have eq51436 : ∀ X0 X1 : G, (M.op y (M.op x (M.op (M.op X0 X1) X0))) = (M.op (M.op x (M.op (M.op X0 X1) X0)) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50501 (M.op (M.op X0 X1) X0)
       have i₂ := eq43919 (M.op (M.op X0 X1) X0) X1 X0
       grind)
    | exact superpose eq43919 eq50501
    | exact resolve eq50501 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50501
  have eq51719 : ∀ X0 X1 : G, (M.op y (M.op x X1)) = (M.op (M.op x X1) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51436 x X1
       have i₂ := eq43919 x X1 x
       grind)
    | exact superpose eq43919 eq51436
    | exact resolve eq51436 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51436
  have eq51875 : ∀ X0 X1 : G, (M.op y (M.op x X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51719 X0 X1
       have i₂ := eq50951 X0 X1 x
       grind)
    | exact superpose eq50951 eq51719
    | exact resolve eq51719 eq50951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50951 eq51719
  have eq52623 : ∀ X0 X1 : G, (M.op y (M.op x (M.op X1 x))) = (M.op (M.op x (M.op X0 X1)) (M.op (M.op X0 x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq51875 (M.op X0 X1) (M.op X1 x)
       have i₂ := eq18301 X0 X1
       grind)
    | exact superpose eq18301 eq51875
    | exact resolve eq51875 eq18301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18301 eq51875
  have eq53053 : ∀ X0 X1 : G, (M.op y (M.op x (M.op X1 x))) = (M.op (M.op x (M.op X0 X1)) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52623 X0 X1
       have i₂ := eq13977 X0 (M.op x (M.op X0 X1))
       grind)
    | exact superpose eq13977 eq52623
    | exact resolve eq52623 eq13977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13977 eq52623
  have eq53205 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op x (M.op X0 X1)) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53053 X0 X1
       have i₂ := eq15397 X1 y
       grind)
    | exact superpose eq15397 eq53053
    | exact resolve eq53053 eq15397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15397 eq53053
  have eq53759 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op x X0) (M.op x (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq53205 (M.op X1 X0) X1
       have i₂ := eq43919 x X0 X1
       grind)
    | exact superpose eq43919 eq53205
    | exact resolve eq53205 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53205
  have eq55269 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op (M.op x X1) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53759 X1 (M.op X1 X0)
       have i₂ := eq43919 x X0 X1
       grind)
    | exact superpose eq43919 eq53759
    | exact resolve eq53759 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55401 : ∀ X0 X1 : G, (M.op y X1) = (M.op y (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq53759 X0 X1
       have i₂ := eq55269 (M.op X1 X0) X0
       grind)
    | exact superpose eq55269 eq53759
    | exact resolve eq53759 eq55269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53759
  have eq56193 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op y X0) y)) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43919 X1 (M.op X2 (M.op X0 X2)) y
       have i₂ := eq55401 X2 X0
       grind)
    | exact superpose eq55401 eq43919
    | exact resolve eq43919 eq55401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55401
  have eq56203 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56193 X0 X1 X2
       have i₂ := eq43919 X1 X0 y
       grind)
    | exact superpose eq43919 eq56193
    | exact resolve eq56193 eq43919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43919 eq56193
  have eq56433 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op (M.op X2 y) (M.op (M.op X0 x) x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56203 (M.op X0 X2) X1 (M.op X2 y)
       have i₂ := eq18369 X0 X2
       grind)
    | exact superpose eq18369 eq56203
    | exact resolve eq56203 eq18369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18369 eq56203
  have eq56907 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op (M.op X2 (M.op X0 x)) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56433 X0 X1 X2
       have i₂ := eq12264 X2 (M.op X0 x)
       grind)
    | exact superpose eq12264 eq56433
    | exact resolve eq56433 eq12264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12264 eq56433
  have eq57042 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op (M.op X2 x) (M.op x X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56907 X0 X1 X2
       have i₂ := eq14028 X2 X0 x
       grind)
    | exact superpose eq14028 eq56907
    | exact resolve eq56907 eq14028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14028 eq56907
  have eq65011 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = (M.op (M.op X1 (M.op (M.op X0 x) (M.op x X0))) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43350 X1 X2 (M.op X0 X0)
       have i₂ := eq14035 X0 X0
       grind)
    | (have i₁ := eq43350 X0 X1 (M.op x x)
       have i₂ := eq14035 x x
       grind)
    | exact superpose eq14035 eq43350
    | exact resolve eq43350 eq14035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14035 eq43350
  have eq65616 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65011 X0 X1 X2
       have i₂ := eq57042 X0 X1 X0
       grind)
    | exact superpose eq57042 eq65011
    | exact resolve eq65011 eq57042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57042 eq65011
  have eq65778 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X2)) X0) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45604 X0 X1 X2
       have i₂ := eq65616 X2 (M.op X1 (M.op (M.op X0 X2) X2)) X0
       grind)
    | exact superpose eq65616 eq45604
    | exact resolve eq45604 eq65616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45604 eq65616
  have eq66236 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65778 X2 (M.op (M.op X0 X1) (M.op X2 X1)) X1
       have i₂ := eq44689 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq44689 eq65778
    | exact resolve eq65778 eq44689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65778
  have eq91660 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ (M.op y y)) X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq66236 (σ (M.op y y)) (σ x) X0
       have i₂ := eq5574
       grind)
    | exact superpose eq5574 eq66236
    | exact resolve eq66236 eq5574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5574 eq66236
  have eq92714 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ (M.op y y)) X0) (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq91660 X0
       have i₂ := eq1002 x
       grind)
    | exact superpose eq1002 eq91660
    | exact resolve eq91660 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91660
  have eq93057 : ∀ X0 : G, (M.op (M.op (σ (M.op y y)) X0) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq92714 X0
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq92714
    | exact resolve eq92714 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92714
  have eq210544 : x ≠ y ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq5671 x
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq5671
    | (have j0 := eq5671 x
       grind)
    | exact resolve eq5671 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5671
  have eq210548 : (M.op (M.op x x) y) = (k (M.op x y) x) ∨ x ≠ y := by
    first
    | (have i₁ := eq210544
       have i₂ := eq5837 x
       grind)
    | exact superpose eq5837 eq210544
    | exact resolve eq210544 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210544
  have eq210553 : (M.op y (M.op x x)) = (k (M.op x y) x) ∨ x ≠ y := by
    first
    | (have i₁ := eq210548
       have i₂ := eq13492 x
       grind)
    | exact superpose eq13492 eq210548
    | exact resolve eq210548 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210548
  have eq210558 : x ≠ y ∨ (M.op y y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq210553
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq210553
    | exact resolve eq210553 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210553
  have eq211533 : (σ (M.op x y)) = (M.op (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq9993 (σ (M.op x y))
       have i₂ := eq1002 (M.op x y)
       grind)
    | exact superpose eq1002 eq9993
    | exact resolve eq9993 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9993
  have eq211581 : (σ (M.op x y)) = (M.op (M.op (σ (M.op (M.op x x) y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq211533
       have i₂ := eq13463 x x
       grind)
    | exact superpose eq13463 eq211533
    | exact resolve eq211533 eq13463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211533
  have eq211601 : (σ (M.op x y)) = (M.op (M.op (σ (M.op y (M.op x x))) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq211581
       have i₂ := eq13492 x
       grind)
    | exact superpose eq13492 eq211581
    | exact resolve eq211581 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211581
  have eq211614 : (σ (M.op x y)) = (M.op (M.op (σ (M.op y y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq211601
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq211601
    | exact resolve eq211601 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211601
  have eq211625 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq211614
       have i₂ := eq93057 (σ (M.op x y))
       grind)
    | exact superpose eq93057 eq211614
    | exact resolve eq211614 eq93057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93057 eq211614
  have eq211653 : (σ (M.op x y)) = (M.op (σ x) (σ (k (M.op x y) x))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq211625
       have i₂ := eq4049 (M.op x y) x
       grind)
    | exact superpose eq4049 eq211625
    | (have j1 := eq4049 (M.op x y) x
       grind)
    | exact resolve eq211625 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049 eq211625
  have eq211731 : x = (M.op (M.op x x) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (k (M.op x y) x))) := by
    first
    | (have i₁ := eq211653
       have i₂ := eq13463 x x
       grind)
    | exact superpose eq13463 eq211653
    | exact resolve eq211653 eq13463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13463 eq211653
  have eq211744 : x = (M.op y (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (k (M.op x y) x))) := by
    first
    | (have i₁ := eq211731
       have i₂ := eq13492 x
       grind)
    | exact superpose eq13492 eq211731
    | exact resolve eq211731 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211731
  have eq211757 : x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (k (M.op x y) x))) := by
    first
    | (have i₁ := eq211744
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq211744
    | exact resolve eq211744 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211744
  have eq217220 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq55269 X0 x
       have i₂ := eq44856 x X0 x
       grind)
    | exact superpose eq44856 eq55269
    | (have j1 := eq44856 x X0 x
       grind)
    | exact resolve eq55269 eq44856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44856 eq55269
  have eq217994 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) (M.op X1 (M.op x X0))) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq44689 y (M.op x X0) X1
       have i₂ := eq217220 X0
       grind)
    | exact superpose eq217220 eq44689
    | (have j1 := eq217220 X0
       grind)
    | exact resolve eq44689 eq217220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44689 eq217220
  have eq218086 : ∀ X0 : G, y = (M.op (M.op X0 X0) x) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq217994 X0 x
       have i₂ := eq44922 X0 X0 x x
       grind)
    | exact superpose eq44922 eq217994
    | (have j0 := eq217994 X0 x
       grind)
    | exact resolve eq217994 eq44922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44922 eq217994
  have eq218190 : y = (M.op (M.op (M.op x y) x) x) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq218086 (M.op x y)
       have i₂ := eq5571 (M.op x y)
       grind)
    | exact superpose eq5571 eq218086
    | (have j0 := eq218086 (M.op x y)
       grind)
    | exact resolve eq218086 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571 eq218086
  have eq218477 : y = (M.op (M.op (M.op x x) x) y) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq218190
       have i₂ := eq15705 x x
       grind)
    | exact superpose eq15705 eq218190
    | exact resolve eq218190 eq15705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15705 eq218190
  have eq218507 : x = y ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq218477
       have i₂ := eq5575 x
       grind)
    | exact superpose eq5575 eq218477
    | exact resolve eq218477 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5575 eq218477
  have eq218520 : (M.op (M.op x x) y) = (k (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq218507
       have i₂ := eq5837 x
       grind)
    | exact superpose eq5837 eq218507
    | exact resolve eq218507 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5837 eq218507
  have eq218527 : (M.op y (M.op x x)) = (k (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq218520
       have i₂ := eq13492 x
       grind)
    | exact superpose eq13492 eq218520
    | exact resolve eq218520 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13492 eq218520
  have eq218533 : (M.op y y) = (k (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq218527
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq218527
    | exact resolve eq218527 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218527
  have eq218537 : (M.op y y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq218533
       have r₂ := eq210558
       grind)
    | exact resolve eq218533 eq210558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210558 eq218533
  have eq218541 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq211757
       have i₂ := eq218537
       grind)
    | exact superpose eq218537 eq211757
    | exact resolve eq211757 eq218537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211757 eq218537
  have eq218554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq218541
       have i₂ := eq9975 (σ x)
       grind)
    | exact superpose eq9975 eq218541
    | exact resolve eq218541 eq9975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218541
  have eq218559 : x = (M.op y y) := by
    first
    | (have r₁ := eq218554
       have r₂ := eq16
       grind)
    | exact resolve eq218554 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218554
  have eq218641 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq9395 X0
       have i₂ := eq218559
       grind)
    | exact superpose eq218559 eq9395
    | exact resolve eq9395 eq218559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9395
  have eq218672 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9975 X0
       have i₂ := eq218559
       grind)
    | exact superpose eq218559 eq9975
    | exact resolve eq9975 eq218559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9975
  have eq218966 : y = (k y x) := by
    first
    | (have i₁ := eq30786
       have i₂ := eq218559
       grind)
    | exact superpose eq218559 eq30786
    | exact resolve eq30786 eq218559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30786
  have eq221422 : y = (M.op y x) := by
    first
    | (have i₁ := eq218966
       have i₂ := eq30485
       grind)
    | exact superpose eq30485 eq218966
    | exact resolve eq218966 eq30485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30485 eq218966
  have eq224994 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq218672 (σ x)
       grind)
    | exact superpose eq218672 eq16
    | exact resolve eq16 eq218672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218672
  have eq229865 : x = (M.op y x) := by
    first
    | (have i₁ := eq218559
       have i₂ := eq218641 y
       grind)
    | exact superpose eq218641 eq218559
    | exact resolve eq218559 eq218641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218559 eq218641
  have eq233647 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq224994
       have i₂ := eq1002 x
       grind)
    | exact superpose eq1002 eq224994
    | exact resolve eq224994 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002 eq224994
  have eq233834 : x = y := by
    first
    | (have i₁ := eq229865
       have i₂ := eq221422
       grind)
    | exact superpose eq221422 eq229865
    | exact resolve eq229865 eq221422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229865
  have eq237668 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq233647
       have i₂ := eq5550
       grind)
    | exact superpose eq5550 eq233647
    | exact resolve eq233647 eq5550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550 eq233647
  have eq242150 : x = (M.op x x) := by
    first
    | (have i₁ := eq221422
       have i₂ := eq233834
       grind)
    | exact superpose eq233834 eq221422
    | exact resolve eq221422 eq233834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221422
  have eq246720 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq237668
       have i₂ := eq233834
       grind)
    | exact superpose eq233834 eq237668
    | exact resolve eq237668 eq233834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233834 eq237668
  have eq251465 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq246720
       have i₂ := eq242150
       grind)
    | exact superpose eq242150 eq246720
    | exact resolve eq246720 eq242150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242150 eq246720
  have eq251466 : False := by grind
  exact eq251466

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq95 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq212 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op sF0 (M.op x X0)) x)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op sF4 (M.op x X0)) x)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq483 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq482 eq57
    | exact resolve eq57 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq527 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq483 eq57
    | exact resolve eq57 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq849 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X0) x
       have i₂ := eq56 X1 X1 X0 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq855 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) X3 X1
       have i₂ := eq56 X3 X1 X0 X2
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1076 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq76
  have eq1337 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1076 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1076
    | (have j0 := eq1076 y X0
       grind)
    | exact resolve eq1076 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1361 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1337 X0
       have i₂ := eq853 (σ X0) sF3
       grind)
    | (have i₁ := eq1337 X0
       have i₂ := eq853 sF3 (σ X0)
       grind)
    | exact superpose eq853 eq1337
    | (have j0 := eq1337 X0
       grind)
    | exact resolve eq1337 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1379 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1361 X0
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq1361
    | (have j0 := eq1361 X0
       grind)
    | exact resolve eq1361 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1361
  have eq1846 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq853 (M.op X1 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq853 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq853 eq481
    | exact resolve eq481 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1891 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq853 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq853 X0 (M.op X1 X2)
       grind)
    | exact superpose eq853 eq491
    | exact resolve eq491 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2198 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq849 X0 X1 X2
       have i₂ := eq853 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | (have i₁ := eq849 X0 X1 X2
       have i₂ := eq853 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq853 eq849
    | exact resolve eq849 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq2482 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2198 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1846 X2 X1 X0
       grind)
    | exact superpose eq1846 eq2198
    | exact resolve eq2198 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq2198
  have eq2619 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq853 (M.op sF0 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq212 X0 X0
       have i₂ := eq853 X0 (M.op sF0 (M.op X0 X0))
       grind)
    | exact superpose eq853 eq212
    | exact resolve eq212 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2704 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq853 (M.op sF4 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq217 X0 X0
       have i₂ := eq853 X0 (M.op sF4 (M.op X0 X0))
       grind)
    | exact superpose eq853 eq217
    | exact resolve eq217 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq853
  have eq4298 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op (M.op x y) (M.op X0 X1))) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq2619 eq57
    | exact resolve eq57 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq4331 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op (M.op (M.op x y) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4298 x X1
       have i₂ := eq1891 (M.op X1 y) (M.op sF0 (M.op x X1)) x
       grind)
    | exact superpose eq1891 eq4298
    | exact resolve eq4298 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298
  have eq4410 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op X0 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4331 X0 X1
       have i₂ := eq2482 X0 (M.op X1 y) (M.op sF0 (M.op X0 X1))
       grind)
    | (have i₁ := eq4331 x X1
       have i₂ := eq2482 (M.op sF0 (M.op x X1)) (M.op X1 y) x
       grind)
    | exact superpose eq2482 eq4331
    | exact resolve eq4331 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331
  have eq5225 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2704 eq57
    | exact resolve eq57 eq2704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2704
  have eq5262 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5225 x X1
       have i₂ := eq1891 (M.op X1 sF3) (M.op sF4 (M.op x X1)) x
       grind)
    | exact superpose eq1891 eq5225
    | exact resolve eq5225 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5225
  have eq5349 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5262 X0 X1
       have i₂ := eq2482 X0 (M.op X1 sF3) (M.op sF4 (M.op X0 X1))
       grind)
    | (have i₁ := eq5262 x X1
       have i₂ := eq2482 (M.op sF4 (M.op x X1)) (M.op X1 sF3) x
       grind)
    | exact superpose eq2482 eq5262
    | exact resolve eq5262 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5262
  have eq12515 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq855 X0 X1 X2 X3
       have i₂ := eq491 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq855 X0 X1 X2 X3
       have i₂ := eq491 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq491 eq855
    | exact resolve eq855 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq855
  have eq12516 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12515 X0 X1 X2 X3
       have i₂ := eq1891 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3)) X2
       grind)
    | exact superpose eq1891 eq12515
    | exact resolve eq12515 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891 eq12515
  have eq12517 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12516 X0 X1 X2 X3
       have i₂ := eq2482 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq12516 X0 X1 X2 X3
       have i₂ := eq2482 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq2482 eq12516
    | exact resolve eq12516 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482 eq12516
  have eq75749 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1379 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1379
    | (have j0 := eq1379 x
       grind)
    | exact resolve eq1379 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq75921 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75749
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq75749
    | exact resolve eq75749 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq75749
  have eq75950 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq75921
    | exact resolve eq75921 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75921
  have eq75959 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq75950
    | exact resolve eq75950 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq75950
  have eq196022 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq507
       grind)
    | exact superpose eq507 eq104
    | exact resolve eq104 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq507
  have eq196034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq196022 eq75959
    | exact resolve eq75959 eq196022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75959 eq196022
  have eq196053 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq196034
       have r₂ := eq28
       grind)
    | exact resolve eq196034 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196034
  have eq196196 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq196053 eq12517
    | exact resolve eq12517 eq196053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196053
  have eq196349 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq5349 eq196196
    | exact resolve eq196196 eq5349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349 eq196196
  have eq196350 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq196349
  have eq196649 : ∀ X0 X1 : G, y = (M.op (M.op X0 y) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12517 y y X1 X0
       have i₂ := eq196350
       grind)
    | exact superpose eq196350 eq12517
    | exact resolve eq12517 eq196350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12517 eq196350
  have eq196802 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4410 eq196649
    | exact resolve eq196649 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410 eq196649
  have eq196803 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq196802
  have eq197174 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq196803 eq30
    | exact resolve eq30 eq196803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq196803
  have eq197383 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq197174
    | exact resolve eq197174 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq197174
  have eq197384 : x = y := by grind
  clear eq197383
  have eq197406 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq197384
       grind)
    | exact superpose eq197384 eq19
    | exact resolve eq19 eq197384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq197407 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq197384
       grind)
    | exact superpose eq197384 eq25
    | exact resolve eq25 eq197384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq197384
  have eq197612 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq197407
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq197407
    | exact resolve eq197407 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq197407
  have eq197649 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq197612 eq27
    | exact resolve eq27 eq197612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq197612
  have eq201557 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq197649 eq69
    | exact resolve eq69 eq197649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq197649
  have eq201918 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq201557
       have i₂ := eq197406
       grind)
    | exact superpose eq197406 eq201557
    | exact resolve eq201557 eq197406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197406 eq201557
  have eq202055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq201918 eq15
    | exact resolve eq15 eq201918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201918
  have eq202131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq202055
    | exact resolve eq202055 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq202055
  have eq202152 : False := by grind
  exact eq202152
