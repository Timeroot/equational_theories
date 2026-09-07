import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3751`: `x ◇ y = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3751 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3751 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3751.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq30 X1 (τ X0)
       grind)
    | exact superpose eq30 eq16
    | (have j1 := eq30 X1 X1
       grind)
    | exact resolve eq16 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq124 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq40
  have eq139 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq234 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq9
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq888 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1124 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1212 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1124 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1124
    | (have j0 := eq1124 X0 X1
       grind)
    | exact resolve eq1124 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq2165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq234
       have i₂ := eq1212 y x
       grind)
    | exact superpose eq1212 eq234
    | (have j1 := eq1212 (σ y) (σ x)
       grind)
    | (have r₁ := eq234
       have r₂ := eq1212 y x
       grind)
    | exact resolve eq234 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq2166 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq234
       have i₂ := eq953 x y
       grind)
    | exact superpose eq953 eq234
    | (have j1 := eq953 x y
       grind)
    | (have r₁ := eq234
       have r₂ := eq953 x y
       grind)
    | exact resolve eq234 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq2167 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2166
  have eq2168 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2165
  have eq2194 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq50 (σ x) (σ x)
       have i₂ := eq2167
       grind)
    | exact superpose eq2167 eq50
    | exact resolve eq50 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2167
  have eq2200 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2194
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq2194
    | exact resolve eq2194 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq3024 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq2200
       grind)
    | exact superpose eq2200 eq9
    | exact resolve eq9 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq3072 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3024
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3024
    | exact resolve eq3024 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3073 : y = (k y y) := by
    first
    | (have j1 := eq84 y y
       grind)
    | (have r₁ := eq3072
       have r₂ := eq84 y y
       grind)
    | exact resolve eq3072 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq3072
  have eq3252 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq264 y
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq264
    | (have j0 := eq264 y
       grind)
    | exact resolve eq264 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq3259 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30 y y
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq30
    | (have j0 := eq30 y x
       grind)
    | exact resolve eq30 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3073
  have eq3263 : y = (M.op y y) := by grind
  clear eq3259
  have eq3266 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3252
  have eq3351 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y y x
       have i₂ := eq3263
       grind)
    | exact superpose eq3263 eq49
    | (have j0 := eq49 y X0 (k y X0)
       grind)
    | exact resolve eq49 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3263
  have eq3557 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq246 y X0
       have i₂ := eq3266
       grind)
    | exact superpose eq3266 eq246
    | (have j0 := eq246 y X0
       grind)
    | exact resolve eq246 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq3586 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq3557 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3557
    | (have j0 := eq3557 X0
       grind)
    | exact resolve eq3557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq5188 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139 x
       have i₂ := eq2168
       grind)
    | exact superpose eq2168 eq139
    | exact resolve eq139 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq2168
  have eq5210 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5188
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5188
    | exact resolve eq5188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188
  have eq5426 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5210
       grind)
    | exact superpose eq5210 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq5210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210
  have eq5437 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq5426
  have eq5832 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq5437
       grind)
    | exact superpose eq5437 eq18
    | exact resolve eq18 eq5437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5437
  have eq6258 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq5832
  have eq15379 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq48 (σ X0) (σ y)
       have i₂ := eq3586 X0
       grind)
    | exact superpose eq3586 eq48
    | (have j1 := eq3586 X0
       grind)
    | exact resolve eq48 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq15827 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq15379 x
       grind)
    | exact superpose eq15379 eq14
    | (have j1 := eq15379 x
       grind)
    | exact resolve eq14 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15379
  have eq16181 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq15827
       have i₂ := eq3351 x
       grind)
    | exact superpose eq3351 eq15827
    | (have j1 := eq3351 x
       grind)
    | exact resolve eq15827 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq16190 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15827
       have i₂ := eq953 y x
       grind)
    | exact superpose eq953 eq15827
    | (have j1 := eq953 x x
       grind)
    | exact resolve eq15827 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq15827
  have eq16195 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by grind
  clear eq16181
  have eq16200 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16190
       have r₂ := eq6258
       grind)
    | exact resolve eq16190 eq6258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6258 eq16190
  have eq16215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq16195
       have i₂ := eq48 y x
       grind)
    | (have i₁ := eq16195
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16195
    | exact resolve eq16195 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16195
  have eq16216 : x = y := by grind
  clear eq16215
  have eq16219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16200
       have i₂ := eq48 y x
       grind)
    | (have i₁ := eq16200
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16200
    | exact resolve eq16200 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq16200
  have eq16220 : x = (M.op x x) := by grind
  clear eq16219
  have eq16444 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16216
       grind)
    | exact superpose eq16216 eq14
    | exact resolve eq14 eq16216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16457 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3266
       have i₂ := eq16216
       grind)
    | exact superpose eq16216 eq3266
    | exact resolve eq3266 eq16216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3266 eq16216
  have eq16479 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16444
       have i₂ := eq16220
       grind)
    | exact superpose eq16220 eq16444
    | exact resolve eq16444 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16220 eq16444
  have eq16480 : False := by grind
  exact eq16480

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op x x) X1
       have i₂ := eq8 x x x
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 (M.op x x) X1
       have r₂ := eq8 x x x
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq33 X0 (σ X1)
       grind)
    | exact superpose eq33 eq20
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq23 X1 X1 X0
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq93 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq64 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq11
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq64 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq64 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq46 X0 (σ X1) X2
       grind)
    | exact superpose eq46 eq20
    | (have j1 := eq46 (τ X0) X1 X2
       grind)
    | exact resolve eq20 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq154 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (k (M.op X0 X1) X3) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 X0 x
       have i₂ := eq38 (M.op X0 X1) x X3
       grind)
    | exact superpose eq38 eq8
    | (have j1 := eq38 (M.op X0 X1) X1 X3
       grind)
    | exact resolve eq8 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq192 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k (M.op X1 X0) X2) ∨ (M.op (M.op X1 X0) X3) = (k (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (M.op X2 X1) X1
       have i₂ := eq41 (M.op X2 X1) X1 X2 X3
       grind)
    | exact superpose eq41 eq11
    | (have j1 := eq41 (M.op X1 X0) X1 X2 X3
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq41 (M.op X1 X1) X1 X1 X3
       grind)
    | exact resolve eq11 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq207 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X1 X0) X2) ∨ (M.op (M.op X1 X0) X3) = (k (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq192 X0 X1 X2 X3
       have j1 := eq154 X1 X0 X3
       grind)
    | (have r₁ := eq192 X0 X1 X2 X3
       have r₂ := eq154 X0 X1 X3
       grind)
    | (have r₁ := eq192 X1 X0 X2 X3
       have r₂ := eq154 X0 X1 X3
       grind)
    | exact resolve eq192 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq192
  have eq238 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq64 (σ X0) X1
       grind)
    | (have i₁ := eq44 X0 X0
       have i₂ := eq64 X0 (σ X0)
       grind)
    | exact superpose eq64 eq44
    | exact resolve eq44 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq245 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x x
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq890 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X1 (M.op X0 X0)
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq238
    | (have j0 := eq238 X1 (M.op X0 X0)
       grind)
    | exact resolve eq238 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq930 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq238 X0 (τ X1)
       grind)
    | exact superpose eq238 eq16
    | (have j1 := eq238 X0 (τ X1)
       grind)
    | exact resolve eq16 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq238
  have eq955 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq963 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq930 X0 X1
       have j1 := eq93 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq930 X0 X1
       have r₂ := eq93 X0 (k (σ (τ X1)) X1) x
       grind)
    | (have r₁ := eq930 X0 X1
       have r₂ := eq93 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq930 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq930
  have eq977 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq963 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq963
    | exact resolve eq963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq985 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | (have j0 := eq42 X1 X1
       grind)
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1055 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq985
    | (have j0 := eq985 X0 X1
       grind)
    | exact resolve eq985 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1066 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq977 x X2
       have i₂ := eq977 x X0
       grind)
    | exact superpose eq977 eq977
    | exact resolve eq977 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq977 X0 (σ X1)
       grind)
    | exact superpose eq977 eq13
    | exact resolve eq13 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 X1
       have i₂ := eq977 X0 (τ X1)
       grind)
    | exact superpose eq977 eq47
    | exact resolve eq47 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1143 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X1)
       have i₂ := eq977 X0 (τ X1)
       grind)
    | exact superpose eq977 eq15
    | exact resolve eq15 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq1146 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1143 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1143
    | exact resolve eq1143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq2357 : ∀ X0 X2 : G, (k X2 X2) = (σ (σ (k X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq1146 x X2
       have i₂ := eq1134 x X0
       grind)
    | exact superpose eq1134 eq1146
    | exact resolve eq1146 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq1146
  have eq3118 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq245
       have i₂ := eq46 x X0 y
       grind)
    | exact superpose eq46 eq245
    | (have j1 := eq46 x X0 x
       grind)
    | exact resolve eq245 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq245
  have eq3122 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq3118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118
  have eq8086 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X1 X0) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq207 X1 X0 X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq20292 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ x) X1
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq51
    | (have j1 := eq3122 X1
       grind)
    | exact resolve eq51 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3122
  have eq20427 : ∀ X0 X1 : G, x = (k x X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20292 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq20292
    | (have j0 := eq20292 X0 X0
       grind)
    | exact resolve eq20292 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20292
  have eq20607 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq20427 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20427
  have eq20608 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq20607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20607
  have eq20949 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq977 X0 x
       have i₂ := eq20608 x
       grind)
    | exact superpose eq20608 eq977
    | exact resolve eq977 eq20608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq20951 : ∀ X0 : G, x = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1066 X0 x
       have i₂ := eq20608 x
       grind)
    | exact superpose eq20608 eq1066
    | exact resolve eq1066 eq20608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq20969 : ∀ X0 : G, (k X0 X0) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2357 x X0
       have i₂ := eq20608 x
       grind)
    | exact superpose eq20608 eq2357
    | exact resolve eq2357 eq20608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357 eq20608
  have eq21530 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq20949 x
       grind)
    | exact superpose eq20949 eq8
    | exact resolve eq8 eq20949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21567 : ∀ X1 : G, x = (τ (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq1141 x X1
       have i₂ := eq20949 x
       grind)
    | exact superpose eq20949 eq1141
    | exact resolve eq1141 eq20949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq21722 : x = (τ (σ (σ x))) := by
    first
    | (have i₁ := eq21567 x
       have i₂ := eq20969 x
       grind)
    | exact superpose eq20969 eq21567
    | exact resolve eq21567 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20969 eq21567
  have eq21797 : x = (σ x) := by
    first
    | (have i₁ := eq21722
       have i₂ := eq9 (σ x)
       grind)
    | exact superpose eq9 eq21722
    | exact resolve eq21722 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21722
  have eq22328 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21797
       grind)
    | exact superpose eq21797 eq14
    | exact resolve eq14 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22331 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq21797
       grind)
    | exact superpose eq21797 eq13
    | exact resolve eq13 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21797
  have eq22640 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20949 X0
       have i₂ := eq1055 X1 X0
       grind)
    | exact superpose eq1055 eq20949
    | (have j1 := eq1055 X1 X0
       grind)
    | exact resolve eq20949 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq20949
  have eq24121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (τ X0) X1
       have i₂ := eq20951 (τ X0)
       grind)
    | exact superpose eq20951 eq107
    | (have j0 := eq107 X0 X1 X1
       grind)
    | exact resolve eq107 eq20951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq20951
  have eq75785 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8086 X1 X0 x
       have i₂ := eq21530 X0 X1
       grind)
    | exact superpose eq21530 eq8086
    | (have j0 := eq8086 X1 X0 x
       grind)
    | (have r₁ := eq8086 X1 X0 x
       have r₂ := eq21530 X0 X1
       grind)
    | exact resolve eq8086 eq21530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086 eq21530
  have eq75833 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have j0 := eq75785 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75785
  have eq330806 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq22331 X0
       have i₂ := eq24121 (σ X0) x
       grind)
    | exact superpose eq24121 eq22331
    | (have j1 := eq24121 (σ X0) x
       grind)
    | exact resolve eq22331 eq24121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24121
  have eq330885 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq330806 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq330806
    | (have j0 := eq330806 X0
       grind)
    | exact resolve eq330806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330806
  have eq530150 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq22640 X0 x
       have i₂ := eq330885 X0
       grind)
    | exact superpose eq330885 eq22640
    | (have j0 := eq22640 X0 x
       have j1 := eq330885 X0
       grind)
    | exact resolve eq22640 eq330885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22640 eq330885
  have eq530175 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq530150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530150
  have eq534164 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (σ (k (M.op X0 x) x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq22331 (M.op X0 x)
       have i₂ := eq530175 X0
       grind)
    | exact superpose eq530175 eq22331
    | (have j1 := eq530175 X0
       grind)
    | exact resolve eq22331 eq530175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22331 eq530175
  have eq534167 : ∀ X0 : G, (σ (M.op x X0)) = (k (M.op (σ X0) x) x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq534164 X0
       have i₂ := eq75833 x X0
       grind)
    | exact superpose eq75833 eq534164
    | (have j0 := eq534164 X0
       grind)
    | exact resolve eq534164 eq75833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534164
  have eq534175 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq534167 X0
       have i₂ := eq75833 x (σ X0)
       grind)
    | exact superpose eq75833 eq534167
    | (have j0 := eq534167 X0
       grind)
    | exact resolve eq534167 eq75833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75833 eq534167
  have eq536926 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq22328
       have i₂ := eq534175 y
       grind)
    | exact superpose eq534175 eq22328
    | (have j1 := eq534175 y
       grind)
    | (have r₁ := eq22328
       have r₂ := eq534175 y
       grind)
    | exact resolve eq22328 eq534175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22328 eq534175
  have eq536943 : x = y := by grind
  clear eq536926
  have eq538101 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq536943
       grind)
    | exact superpose eq536943 eq14
    | exact resolve eq14 eq536943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536943
  have eq538107 : False := by grind
  exact eq538107

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_y_pxy_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op x x) X1
       have r₂ := eq8 x x x
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq20 X1 (τ X0)
       grind)
    | exact superpose eq20 eq16
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X1 X0
       have i₂ := eq12 X0 X3
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq21 X1 X1 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq111 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (k (τ X1) X2) = (M.op (τ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq31 (τ X1) X0 X2
       grind)
    | exact superpose eq31 eq15
    | (have j1 := eq31 X1 (σ X0) X2
       grind)
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq31 X0 X2 (τ X1)
       grind)
    | exact superpose eq31 eq16
    | (have j1 := eq31 X0 X2 X2
       grind)
    | exact resolve eq16 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq63 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X0
       have i₂ := eq63 X0 (σ X0)
       grind)
    | exact superpose eq63 eq29
    | exact resolve eq29 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x x
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq894 : ∀ X0 X1 X2 : G, (k (k (σ (τ X0)) X0) X1) = X1 ∨ (k (τ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq112 (τ X0) X0 X2
       grind)
    | exact superpose eq112 eq47
    | (have j1 := eq112 (k (σ (τ X0)) X0) X1 X1
       grind)
    | exact resolve eq47 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq112
  have eq941 : ∀ X0 X1 X2 : G, (k (k X0 X0) X1) = X1 ∨ (k (τ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq894 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq894
    | (have j0 := eq894 X0 X1 X2
       grind)
    | exact resolve eq894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1059 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq293 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq293
    | (have j0 := eq293 (τ X0)
       grind)
    | exact resolve eq293 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq1071 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1059 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1059
    | (have j0 := eq1059 X0
       grind)
    | exact resolve eq1059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1078 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1071 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1071
    | (have j0 := eq1071 X0
       grind)
    | exact resolve eq1071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1451 : ∀ X0 X1 X2 X3 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X2 (τ (σ X0))))) ∨ (k (τ (σ X2)) X3) = (M.op (τ (σ X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X2 (σ X0) X1
       have i₂ := eq111 X0 (σ X2) X3
       grind)
    | exact superpose eq111 eq42
    | (have j1 := eq111 X0 (σ X2) X3
       grind)
    | exact resolve eq42 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq111
  have eq1481 : ∀ X0 X1 X2 X3 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X2 X0))) ∨ (k (τ (σ X2)) X3) = (M.op (τ (σ X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1451 X0 X1 X2 X3
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1451
    | (have j0 := eq1451 X0 X1 X2 X3
       grind)
    | exact resolve eq1451 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1499 : ∀ X0 X1 X2 X3 : G, (σ (k X1 X0)) = (σ (k X1 (k X2 X0))) ∨ (k (τ (σ X2)) X3) = (M.op (τ (σ X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1481 X0 X1 X2 X3
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1481
    | (have j0 := eq1481 X0 X1 X2 X3
       grind)
    | exact resolve eq1481 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1502 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ (σ (k X1 X0)) = (σ (k X1 (k X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1499 X0 X1 X0 X3
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1499
    | (have j0 := eq1499 X0 X1 X2 X3
       grind)
    | exact resolve eq1499 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq2042 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k (k X1 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (τ X1)
       have i₂ := eq941 X1 X2 (τ X0)
       grind)
    | exact superpose eq941 eq16
    | (have j1 := eq941 X1 X2 X2
       grind)
    | exact resolve eq16 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq2045 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X1 X0) ∨ (k (k X1 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2042 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2042
    | (have j0 := eq2042 X0 X1 X2
       grind)
    | exact resolve eq2042 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq2061 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k (k X1 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2045 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2045
    | (have j0 := eq2045 X0 X1 X2
       grind)
    | exact resolve eq2045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2500 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq265
       have i₂ := eq31 x X0 y
       grind)
    | exact superpose eq31 eq265
    | (have j1 := eq31 x X0 x
       grind)
    | exact resolve eq265 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq265
  have eq2503 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2558 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq2503 (τ X0)
       grind)
    | exact superpose eq2503 eq16
    | exact resolve eq16 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq2561 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2558 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2558
    | exact resolve eq2558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2574 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2561 X0
       have j1 := eq11 (σ x) X0
       grind)
    | (have r₁ := eq2561 X0
       have r₂ := eq11 (σ x) x
       grind)
    | exact resolve eq2561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2725 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (σ x) X0
       have i₂ := eq2574 (σ X0)
       grind)
    | exact superpose eq2574 eq36
    | exact resolve eq36 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2730 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq2725 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2725
    | exact resolve eq2725 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2737 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2730 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2730
    | exact resolve eq2730 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq3047 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1078 x
       have i₂ := eq2737 x
       grind)
    | exact superpose eq2737 eq1078
    | (have j0 := eq1078 x
       grind)
    | (have r₁ := eq1078 x
       have r₂ := eq2737 x
       grind)
    | exact resolve eq1078 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3061 : ∀ X0 : G, (τ (σ X0)) = (k (τ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 x X0
       have i₂ := eq2737 (σ X0)
       grind)
    | exact superpose eq2737 eq36
    | exact resolve eq36 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2737
  have eq3064 : x = (M.op x x) := by grind
  clear eq3047
  have eq3066 : ∀ X0 : G, (k (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3061 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3061
    | exact resolve eq3061 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061
  have eq3102 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq3064
       grind)
    | exact superpose eq3064 eq8
    | exact resolve eq8 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3111 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq63 X0 x
       have i₂ := eq3064
       grind)
    | exact superpose eq3064 eq63
    | exact resolve eq63 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq3123 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 x x x
       have i₂ := eq3064
       grind)
    | exact superpose eq3064 eq58
    | (have j0 := eq58 X0 X1 x X1
       grind)
    | exact resolve eq58 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq3064
  have eq3686 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq1078 (τ x)
       have i₂ := eq3066 (τ x)
       grind)
    | exact superpose eq3066 eq1078
    | (have j0 := eq1078 (τ x)
       grind)
    | (have r₁ := eq1078 (τ x)
       have r₂ := eq3066 (τ x)
       grind)
    | exact resolve eq1078 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq3066
  have eq3705 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq3686
  have eq3717 : x = (τ x) := by
    first
    | (have i₁ := eq3705
       have i₂ := eq3111 (τ x)
       grind)
    | exact superpose eq3111 eq3705
    | exact resolve eq3705 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq3923 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq3717
       grind)
    | exact superpose eq3717 eq10
    | exact resolve eq10 eq3717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3925 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0
       have i₂ := eq3717
       grind)
    | exact superpose eq3717 eq16
    | exact resolve eq16 eq3717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3717
  have eq4106 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3923
       grind)
    | exact superpose eq3923 eq14
    | exact resolve eq14 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq19960 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X1)
       have i₂ := eq258 X0 (τ X1)
       grind)
    | exact superpose eq258 eq15
    | (have j1 := eq258 X0 (τ X1)
       grind)
    | exact resolve eq15 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq258
  have eq20082 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19960 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq19960
    | (have j0 := eq19960 X0 X1
       grind)
    | exact resolve eq19960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19960
  have eq20292 : ∀ X0 X1 : G, x = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20082 X0 X1
       have i₂ := eq3111 X0
       grind)
    | exact superpose eq3111 eq20082
    | (have j0 := eq20082 X0 X1
       grind)
    | exact resolve eq20082 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20082
  have eq20405 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ x = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20292 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq20292
    | (have j0 := eq20292 X0 X1
       grind)
    | exact resolve eq20292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20292
  have eq20443 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 := by
    intro X1
    first
    | (have i₁ := eq20405 x X1
       have i₂ := eq3111 x
       grind)
    | exact superpose eq3111 eq20405
    | (have j0 := eq20405 x X1
       grind)
    | exact resolve eq20405 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111 eq20405
  have eq20642 : ∀ X0 X1 : G, x = (k X0 X0) ∨ (k X0 X1) = X1 ∨ x = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2061 X1 X0 (k X0 X0)
       have i₂ := eq20443 (k X0 X0)
       grind)
    | exact superpose eq20443 eq2061
    | (have j0 := eq2061 X1 X0 x
       have j1 := eq20443 X0
       grind)
    | exact resolve eq2061 eq20443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq20649 : ∀ X0 X1 : G, x = (k X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20642
  have eq26657 : ∀ X0 : G, x ≠ X0 ∨ x = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20649 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20649
  have eq26663 : ∀ X0 : G, x = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26657 X0
       have j1 := eq20443 X0
       grind)
    | (have r₁ := eq26657 (k x x)
       have r₂ := eq20443 x
       grind)
    | (have r₁ := eq26657 x
       have r₂ := eq20443 x
       grind)
    | (have r₁ := eq26657 x
       have r₂ := eq20443 x
       grind)
    | exact resolve eq26657 eq20443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20443 eq26657
  have eq92368 : ∀ X0 X1 X2 X3 : G, (τ (σ (k X0 X1))) = (k X0 (k X2 X1)) ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (k X0 (k X2 X1))
       have i₂ := eq1502 X1 X0 X2 X3
       grind)
    | exact superpose eq1502 eq9
    | (have j1 := eq1502 X0 X1 X2 X3
       grind)
    | exact resolve eq9 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq92505 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (k X0 (k X2 X1)) ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92368 X0 X1 X2 X3
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq92368
    | (have j0 := eq92368 X0 X1 X2 X3
       grind)
    | exact resolve eq92368 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92368
  have eq1886726 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 x) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92505 X0 X1 X1 X2
       have i₂ := eq26663 X1
       grind)
    | exact superpose eq26663 eq92505
    | (have j0 := eq92505 X0 X1 X1 X2
       grind)
    | exact resolve eq92505 eq26663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92505
  have eq1889942 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1886726 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886726
  have eq1889945 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1889942 X0
       have i₂ := eq26663 X0
       grind)
    | exact superpose eq26663 eq1889942
    | (have j0 := eq1889942 X0
       grind)
    | exact resolve eq1889942 eq26663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26663 eq1889942
  have eq1890113 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1889945 X0
       have j1 := eq3123 X0 x
       grind)
    | (have r₁ := eq1889945 X0
       have r₂ := eq3123 X0 x
       grind)
    | exact resolve eq1889945 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123 eq1889945
  have eq1892142 : ∀ X0 : G, (M.op (σ X0) x) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq3925 X0
       have i₂ := eq1890113 (σ X0)
       grind)
    | exact superpose eq1890113 eq3925
    | exact resolve eq3925 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1892491 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1892142 X0
       have i₂ := eq1890113 X0
       grind)
    | exact superpose eq1890113 eq1892142
    | exact resolve eq1892142 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892142
  have eq1896392 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1892491 (M.op X1 X0)
       have i₂ := eq3102 X0 X1
       grind)
    | exact superpose eq3102 eq1892491
    | exact resolve eq1892491 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896612 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (σ (k (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq3925 (M.op X0 x)
       have i₂ := eq1892491 X0
       grind)
    | exact superpose eq1892491 eq3925
    | exact resolve eq3925 eq1892491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925
  have eq1896640 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq1896612 X0
       have i₂ := eq1890113 (M.op X0 x)
       grind)
    | exact superpose eq1890113 eq1896612
    | exact resolve eq1896612 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896612
  have eq1896787 : ∀ X0 : G, (k (M.op (σ X0) x) x) = (M.op (σ (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq1896640 X0
       have i₂ := eq1892491 (M.op X0 x)
       grind)
    | exact superpose eq1892491 eq1896640
    | exact resolve eq1896640 eq1892491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892491 eq1896640
  have eq1896862 : ∀ X0 : G, (σ (M.op x X0)) = (k (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq1896787 X0
       have i₂ := eq1896392 x X0
       grind)
    | exact superpose eq1896392 eq1896787
    | exact resolve eq1896787 eq1896392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896392 eq1896787
  have eq1896885 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq1896862 X0
       have i₂ := eq1890113 (M.op (σ X0) x)
       grind)
    | exact superpose eq1890113 eq1896862
    | exact resolve eq1896862 eq1890113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890113 eq1896862
  have eq1896895 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1896885 X0
       have i₂ := eq3102 x (σ X0)
       grind)
    | exact superpose eq3102 eq1896885
    | exact resolve eq1896885 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102 eq1896885
  have eq1903003 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq4106
       have i₂ := eq1896895 y
       grind)
    | exact superpose eq1896895 eq4106
    | (have r₁ := eq4106
       have r₂ := eq1896895 y
       grind)
    | exact resolve eq4106 eq1896895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106 eq1896895
  have eq1903097 : False := by grind
  exact eq1903097

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pyx_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X1 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq21 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq21 X1 X1 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq160 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (M.op X0 X0)
       have i₂ := eq96 X0 (σ X1)
       grind)
    | exact superpose eq96 eq42
    | exact resolve eq42 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq68 (σ X0) X1
       grind)
    | (have i₁ := eq34 X0 X0
       have i₂ := eq68 X0 (σ X0)
       grind)
    | exact superpose eq68 eq34
    | exact resolve eq34 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq34 X2 X0
       grind)
    | exact superpose eq34 eq13
    | (have j1 := eq34 X2 X0
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 (σ X2)
       have i₂ := eq34 X0 X2
       grind)
    | exact superpose eq34 eq68
    | (have j1 := eq34 X0 X2
       grind)
    | exact resolve eq68 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq359 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X2)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq332 X0 X1 X2
       have i₂ := eq96 (σ X0) (σ X1)
       grind)
    | exact superpose eq96 eq332
    | (have j0 := eq332 X0 X1 X2
       grind)
    | exact resolve eq332 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq467 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ (M.op X0 X0))
       have i₂ := eq160 X0 (σ X1)
       grind)
    | exact superpose eq160 eq42
    | exact resolve eq42 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq160
  have eq991 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq467 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq467 eq300
    | (have j0 := eq300 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq300 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq992 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X1 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq300
    | (have j0 := eq300 X1 (M.op X0 X0)
       grind)
    | exact resolve eq300 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1029 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq300 X0 (τ X1)
       grind)
    | exact superpose eq300 eq17
    | (have j1 := eq300 X0 (τ X1)
       grind)
    | exact resolve eq17 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq1046 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq992 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1047 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq991 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1061 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1029 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1029
    | (have j0 := eq1029 X0 X1
       grind)
    | exact resolve eq1029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1071 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq1047
    | exact resolve eq1047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1074 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1061 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1061
    | (have j0 := eq1061 X0 X1
       grind)
    | exact resolve eq1061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1328 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1071 x X1
       have i₂ := eq1071 X0 x
       grind)
    | exact superpose eq1071 eq1071
    | exact resolve eq1071 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1403 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1403 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1403
    | (have j0 := eq1403 X0 X1
       grind)
    | exact resolve eq1403 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq9547 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (M.op (σ (τ X2)) (σ X0)) = (σ (k X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 X1
       have i₂ := eq359 X0 X1 (τ X2)
       grind)
    | exact superpose eq359 eq17
    | (have j1 := eq359 X0 X1 (τ X2)
       grind)
    | exact resolve eq17 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq9711 : ∀ X0 X1 X2 : G, (k (σ X0) X2) = (M.op (σ (τ X2)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9547 X0 X1 X2
       have i₂ := eq17 X2 X0
       grind)
    | exact superpose eq17 eq9547
    | (have j0 := eq9547 X0 X1 X2
       grind)
    | exact resolve eq9547 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq9547
  have eq9774 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9711 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq9711
    | (have j0 := eq9711 X0 X1 X2
       grind)
    | exact resolve eq9711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711
  have eq9870 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 X2
       have i₂ := eq1074 X2 X0
       grind)
    | exact superpose eq1074 eq68
    | (have j1 := eq1074 X1 X0
       grind)
    | exact resolve eq68 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1074
  have eq12152 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq96 X2 x
       have i₂ := eq9870 X0 x X2
       grind)
    | (have i₁ := eq96 X0 x
       have i₂ := eq9870 (M.op X0 X0) x X2
       grind)
    | exact superpose eq9870 eq96
    | (have j1 := eq9870 X0 X3 X2
       grind)
    | exact resolve eq96 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq13496 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12152 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12152
  have eq13506 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13496 X0 X1
       have j1 := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 (k X0 X0) X1
       have r₂ := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 X0 x
       have r₂ := eq9870 X0 X1 x
       grind)
    | (have r₁ := eq13496 (M.op x x) X1
       have r₂ := eq9870 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq13496 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9870 eq13496
  have eq14216 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1328 x X1
       have i₂ := eq13506 X0 x
       grind)
    | exact superpose eq13506 eq1328
    | exact resolve eq1328 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq14360 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X1
       have i₂ := eq13506 (τ X1) X0
       grind)
    | exact superpose eq13506 eq51
    | exact resolve eq51 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq13506
  have eq37974 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1046 X2 X1
       have i₂ := eq1509 X0 X2
       grind)
    | (have i₁ := eq1046 X0 X1
       have i₂ := eq1509 (M.op X0 X0) X1
       grind)
    | exact superpose eq1509 eq1046
    | (have j1 := eq1509 X0 X2
       grind)
    | exact resolve eq1046 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq1509
  have eq55782 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq346 x X0 y
       grind)
    | exact superpose eq346 eq14
    | (have j1 := eq346 x X0 x
       grind)
    | exact resolve eq14 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq55990 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq55782 X0
       have j1 := eq37974 x X0 x
       grind)
    | (have r₁ := eq55782 X0
       have r₂ := eq37974 x x y
       grind)
    | exact resolve eq55782 eq37974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37974 eq55782
  have eq56252 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1071 x X0
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq1071
    | exact resolve eq1071 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq56314 : ∀ X1 : G, (σ x) = (τ (τ (k X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq14216 X1 x
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq14216
    | exact resolve eq14216 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14216
  have eq56330 : ∀ X1 : G, (σ x) = (τ (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq14360 x X1
       have i₂ := eq55990 x
       grind)
    | exact superpose eq55990 eq14360
    | exact resolve eq14360 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14360
  have eq56478 : (σ x) = (τ (σ x)) := by
    first
    | (have i₁ := eq56314 x
       have i₂ := eq56330 x
       grind)
    | exact superpose eq56330 eq56314
    | exact resolve eq56314 eq56330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56314 eq56330
  have eq56521 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq56252 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq56252
    | exact resolve eq56252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56252
  have eq56566 : x = (σ x) := by
    first
    | (have i₁ := eq56478
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq56478
    | exact resolve eq56478 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56478
  have eq57545 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq14
    | exact resolve eq14 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57547 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq13
    | exact resolve eq13 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59980 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq56521 x
       grind)
    | exact superpose eq56521 eq8
    | exact resolve eq8 eq56521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60102 : ∀ X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ x = (M.op X1 x) := by
    intro X1 X2
    first
    | (have i₁ := eq62 x x x x
       have i₂ := eq56521 x
       grind)
    | exact superpose eq56521 eq62
    | (have j0 := eq62 X1 X1 X2 X2
       grind)
    | exact resolve eq62 eq56521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq56521
  have eq99184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9774 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9774
  have eq99185 : ∀ X0 X1 : G, (σ x) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99184 X0 X1
       have i₂ := eq55990 (σ X0)
       grind)
    | exact superpose eq55990 eq99184
    | (have j0 := eq99184 X0 X1
       grind)
    | exact resolve eq99184 eq55990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55990 eq99184
  have eq99279 : ∀ X0 X1 : G, x ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99185 X0 X1
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq99185
    | (have j0 := eq99185 X0 X1
       grind)
    | exact resolve eq99185 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99185
  have eq530757 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq99279 x x
       have i₂ := eq56566
       grind)
    | exact superpose eq56566 eq99279
    | exact resolve eq99279 eq56566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56566 eq99279
  have eq530788 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq530757 X0
       have j1 := eq60102 X0 x
       grind)
    | (have r₁ := eq530757 x
       have r₂ := eq60102 x x
       grind)
    | exact resolve eq530757 eq60102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60102 eq530757
  have eq530918 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq57547 X0
       have i₂ := eq530788 (σ X0)
       grind)
    | exact superpose eq530788 eq57547
    | exact resolve eq57547 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531338 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq530918 X0
       have i₂ := eq530788 X0
       grind)
    | exact superpose eq530788 eq530918
    | exact resolve eq530918 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530918
  have eq531457 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq531338 (M.op X1 X0)
       have i₂ := eq59980 X0 X1
       grind)
    | exact superpose eq59980 eq531338
    | exact resolve eq531338 eq59980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531668 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (k x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq57547 (M.op X0 x)
       have i₂ := eq531338 X0
       grind)
    | exact superpose eq531338 eq57547
    | exact resolve eq57547 eq531338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57547
  have eq531686 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq531668 X0
       have i₂ := eq530788 (M.op X0 x)
       grind)
    | exact superpose eq530788 eq531668
    | exact resolve eq531668 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531668
  have eq531868 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (M.op (σ (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq531686 X0
       have i₂ := eq531338 (M.op X0 x)
       grind)
    | exact superpose eq531338 eq531686
    | exact resolve eq531686 eq531338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531338 eq531686
  have eq531989 : ∀ X0 : G, (σ (M.op x X0)) = (k x (M.op (σ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq531868 X0
       have i₂ := eq531457 x X0
       grind)
    | exact superpose eq531457 eq531868
    | exact resolve eq531868 eq531457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531457 eq531868
  have eq532078 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq531989 X0
       have i₂ := eq530788 (M.op (σ X0) x)
       grind)
    | exact superpose eq530788 eq531989
    | exact resolve eq531989 eq530788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530788 eq531989
  have eq532145 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq532078 X0
       have i₂ := eq59980 x (σ X0)
       grind)
    | exact superpose eq59980 eq532078
    | exact resolve eq532078 eq59980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59980 eq532078
  have eq533480 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq57545
       have i₂ := eq532145 y
       grind)
    | exact superpose eq532145 eq57545
    | (have r₁ := eq57545
       have r₂ := eq532145 y
       grind)
    | exact resolve eq57545 eq532145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57545 eq532145
  have eq533649 : False := by grind
  exact eq533649

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3756 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3756 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X1 X0) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (τ X0) X1) X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X2 X1 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq21 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq21 X1 X1 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq97 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    grind
  have eq311 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (M.op X1 X1)
       have i₂ := eq97 X1 (σ X0)
       grind)
    | exact superpose eq97 eq43
    | exact resolve eq43 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq311 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq311
    | exact resolve eq311 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq348 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq69 (σ X0) X1
       grind)
    | (have i₁ := eq35 X0 X0
       have i₂ := eq69 X0 (σ X0)
       grind)
    | exact superpose eq69 eq35
    | exact resolve eq35 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 (σ X2)
       have i₂ := eq35 X0 X2
       grind)
    | exact superpose eq35 eq69
    | (have j1 := eq35 X0 X2
       grind)
    | exact resolve eq69 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq441 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (τ (M.op X1 X1))
       have i₂ := eq332 (σ X0) X1
       grind)
    | exact superpose eq332 eq43
    | exact resolve eq43 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq444 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq441
    | exact resolve eq441 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq484 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (τ (τ (M.op X1 X1)))
       have i₂ := eq444 (σ X0) X1
       grind)
    | exact superpose eq444 eq43
    | exact resolve eq43 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq487 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq484
    | exact resolve eq484 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq742 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (k (k (τ (σ X0)) X0) X1)) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (σ X0) X0 X1
       have i₂ := eq47 (σ X0) X2
       grind)
    | exact superpose eq47 eq25
    | (have j1 := eq47 (σ X0) X2
       grind)
    | exact resolve eq25 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47
  have eq802 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 X0) X1)) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq742 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq742
    | (have j0 := eq742 X0 X1 X2
       grind)
    | exact resolve eq742 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq809 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (k (k X0 X0) X1)) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq802 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq802
    | (have j0 := eq802 X0 X1 X2
       grind)
    | exact resolve eq802 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq1130 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq405 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq405
    | (have j0 := eq405 (M.op X0 X0)
       grind)
    | exact resolve eq405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq1136 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1130 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1201 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1311 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1201 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1201
    | (have j0 := eq1201 X0 X1
       grind)
    | exact resolve eq1201 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq2946 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq444 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq444 eq348
    | (have j0 := eq348 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq348 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq2947 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (τ (M.op X0 X0))))) ∨ (M.op X1 X1) = (σ (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X1 (τ (τ (τ (M.op X0 X0))))
       have i₂ := eq487 (τ (τ (τ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq487 eq348
    | (have j0 := eq348 X1 (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact resolve eq348 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq2952 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X1 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq348
    | (have j0 := eq348 X1 (M.op X0 X0)
       grind)
    | exact resolve eq348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3011 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq348 X0 (τ X1)
       grind)
    | exact superpose eq348 eq17
    | (have j1 := eq348 X0 (τ X1)
       grind)
    | exact resolve eq17 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq3039 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2952 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq3044 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq2947 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq3045 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq2946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq3065 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3011 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3011
    | (have j0 := eq3011 X0 X1
       grind)
    | exact resolve eq3011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3089 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3044 X0 X1
       have i₂ := eq10 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq10 eq3044
    | exact resolve eq3044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3090 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3045 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq3045
    | exact resolve eq3045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3092 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3065 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3065
    | (have j0 := eq3065 X0 X1
       grind)
    | exact resolve eq3065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065
  have eq15851 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 X2
       have i₂ := eq3092 X2 X0
       grind)
    | exact superpose eq3092 eq69
    | (have j1 := eq3092 X1 X0
       grind)
    | exact resolve eq69 eq3092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3092
  have eq18860 : ∀ X0 X1 X3 : G, (k X1 X0) = X1 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq97 x X1
       have i₂ := eq15851 X0 X3 x
       grind)
    | (have i₁ := eq97 X0 X1
       have i₂ := eq15851 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq15851 eq97
    | (have j1 := eq15851 X0 X3 x
       grind)
    | exact resolve eq97 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq21783 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq18860 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860
  have eq21793 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq21783 X0 X1
       have j1 := eq15851 X0 X1 x
       grind)
    | (have r₁ := eq21783 (k X0 X0) X1
       have r₂ := eq15851 X0 X1 x
       grind)
    | (have r₁ := eq21783 X0 x
       have r₂ := eq15851 X0 X1 x
       grind)
    | (have r₁ := eq21783 (M.op x x) X1
       have r₂ := eq15851 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq21783 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851 eq21783
  have eq22903 : ∀ X0 X2 : G, (k X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq3039 X2 x
       have i₂ := eq21793 X0 x
       grind)
    | exact superpose eq21793 eq3039
    | exact resolve eq3039 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22914 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3089 x X1
       have i₂ := eq21793 X0 x
       grind)
    | exact superpose eq21793 eq3089
    | exact resolve eq3089 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq23111 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X1
       have i₂ := eq21793 (τ X1) X0
       grind)
    | exact superpose eq21793 eq52
    | exact resolve eq52 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq21793
  have eq37231 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3039 X2 X1
       have i₂ := eq1311 X0 X2
       grind)
    | (have i₁ := eq3039 X0 X1
       have i₂ := eq1311 (M.op X0 X0) X1
       grind)
    | exact superpose eq1311 eq3039
    | (have j1 := eq1311 X0 X2
       grind)
    | exact resolve eq3039 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311 eq3039
  have eq60053 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq398 x X0 y
       grind)
    | exact superpose eq398 eq14
    | (have j1 := eq398 x X0 x
       grind)
    | exact resolve eq14 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq60268 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq60053 X0
       have j1 := eq37231 x X0 x
       grind)
    | (have r₁ := eq60053 X0
       have r₂ := eq37231 x x y
       grind)
    | exact resolve eq60053 eq37231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37231 eq60053
  have eq60540 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3090 x X0
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq3090
    | exact resolve eq3090 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090
  have eq60584 : ∀ X0 : G, (k X0 X0) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq22903 X0 x
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq22903
    | exact resolve eq22903 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22903
  have eq60589 : ∀ X1 : G, (σ x) = (τ (τ (k X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq22914 X1 x
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq22914
    | exact resolve eq22914 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22914
  have eq60601 : ∀ X1 : G, (σ x) = (τ (k X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq23111 x X1
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq23111
    | exact resolve eq23111 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23111
  have eq60687 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1136 X0
       have i₂ := eq60268 (σ (M.op X0 X0))
       grind)
    | exact superpose eq60268 eq1136
    | exact resolve eq1136 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq60710 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq60687 x
       have i₂ := eq60268 x
       grind)
    | exact superpose eq60268 eq60687
    | exact resolve eq60687 eq60268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60268 eq60687
  have eq60747 : (σ x) = (τ (σ x)) := by
    first
    | (have i₁ := eq60589 x
       have i₂ := eq60601 x
       grind)
    | exact superpose eq60601 eq60589
    | exact resolve eq60589 eq60601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60589 eq60601
  have eq60779 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq60540 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq60540
    | exact resolve eq60540 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60540
  have eq60836 : x = (σ x) := by
    first
    | (have i₁ := eq60747
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq60747
    | exact resolve eq60747 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60747
  have eq61750 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq14
    | exact resolve eq14 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61752 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq13
    | exact resolve eq13 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65398 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq60779 x
       grind)
    | exact superpose eq60779 eq8
    | exact resolve eq8 eq60779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65526 : ∀ X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ x = (M.op X1 x) := by
    intro X1 X2
    first
    | (have i₁ := eq63 x x x x
       have i₂ := eq60779 x
       grind)
    | exact superpose eq60779 eq63
    | (have j0 := eq63 X1 X1 X2 X2
       grind)
    | exact resolve eq63 eq60779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq60779
  have eq216782 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k (k X0 X0) X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (k (k X0 X0) X1)
       have i₂ := eq809 X0 X1 X2
       grind)
    | exact superpose eq809 eq9
    | (have j1 := eq809 X0 X1 X2
       grind)
    | exact resolve eq9 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq216785 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k (σ (σ x)) X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216782 X0 X1 X2
       have i₂ := eq60584 X0
       grind)
    | exact superpose eq60584 eq216782
    | (have j0 := eq216782 X0 X1 X2
       grind)
    | exact resolve eq216782 eq60584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216782
  have eq216826 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k (σ x) X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216785 X0 X1 X2
       have i₂ := eq60710
       grind)
    | exact superpose eq60710 eq216785
    | (have j0 := eq216785 X0 X1 X2
       grind)
    | exact resolve eq216785 eq60710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216785
  have eq216838 : ∀ X0 X1 X2 : G, (τ (σ (k X0 X1))) = (k x X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216826 X0 X1 X2
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq216826
    | (have j0 := eq216826 X0 X1 X2
       grind)
    | exact resolve eq216826 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216826
  have eq216843 : ∀ X0 X1 X2 : G, (k X0 X1) = (k x X1) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216838 X0 X1 X2
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq216838
    | (have j0 := eq216838 X0 X1 X2
       grind)
    | exact resolve eq216838 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216838
  have eq1236483 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k (τ X0) X2) = (k x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216843 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq216843
    | (have j0 := eq216843 (τ X0) X2 X2
       grind)
    | exact resolve eq216843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216843
  have eq1237145 : ∀ X0 X1 X2 : G, (k (σ (τ X1)) X0) = (σ (k x (τ X0))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq1236483 X1 X2 (τ X0)
       grind)
    | exact superpose eq1236483 eq17
    | (have j1 := eq1236483 X1 X2 X2
       grind)
    | exact resolve eq17 eq1236483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236483
  have eq1237174 : ∀ X0 X1 X2 : G, (k (σ (τ X1)) X0) = (k (σ x) X0) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1237145 X0 X1 X2
       have i₂ := eq17 X0 x
       grind)
    | exact superpose eq17 eq1237145
    | (have j0 := eq1237145 X0 X1 X2
       grind)
    | exact resolve eq1237145 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1237145
  have eq1237325 : ∀ X0 X1 X2 : G, (k (σ (τ X1)) X0) = (k x X0) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1237174 X0 X1 X2
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq1237174
    | (have j0 := eq1237174 X0 X1 X2
       grind)
    | exact resolve eq1237174 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237174
  have eq1237426 : ∀ X0 X1 X2 : G, (k X1 X0) = (k x X0) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1237325 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1237325
    | (have j0 := eq1237325 X0 X1 X2
       grind)
    | exact resolve eq1237325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237325
  have eq1238128 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1237426 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237426
  have eq1238131 : ∀ X0 : G, (σ (σ x)) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1238128 X0
       have i₂ := eq60584 X0
       grind)
    | exact superpose eq60584 eq1238128
    | (have j0 := eq1238128 X0
       grind)
    | exact resolve eq1238128 eq60584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60584 eq1238128
  have eq1238516 : ∀ X0 : G, (σ x) ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1238131 X0
       have i₂ := eq60710
       grind)
    | exact superpose eq60710 eq1238131
    | (have j0 := eq1238131 X0
       grind)
    | exact resolve eq1238131 eq60710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60710 eq1238131
  have eq1238680 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1238516 X0
       have i₂ := eq60836
       grind)
    | exact superpose eq60836 eq1238516
    | (have j0 := eq1238516 X0
       grind)
    | exact resolve eq1238516 eq60836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60836 eq1238516
  have eq1238802 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1238680 X0
       have j1 := eq65526 X0 x
       grind)
    | (have r₁ := eq1238680 x
       have r₂ := eq65526 x x
       grind)
    | exact resolve eq1238680 eq65526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65526 eq1238680
  have eq1239276 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq61752 X0
       have i₂ := eq1238802 (σ X0)
       grind)
    | exact superpose eq1238802 eq61752
    | exact resolve eq61752 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1240159 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1239276 X0
       have i₂ := eq1238802 X0
       grind)
    | exact superpose eq1238802 eq1239276
    | exact resolve eq1239276 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239276
  have eq1241062 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X1 X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq1240159 (M.op X1 X0)
       have i₂ := eq65398 X0 X1
       grind)
    | exact superpose eq65398 eq1240159
    | exact resolve eq1240159 eq65398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1241486 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (k x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq61752 (M.op X0 x)
       have i₂ := eq1240159 X0
       grind)
    | exact superpose eq1240159 eq61752
    | exact resolve eq61752 eq1240159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61752
  have eq1241508 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (σ (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq1241486 X0
       have i₂ := eq1238802 (M.op X0 x)
       grind)
    | exact superpose eq1238802 eq1241486
    | exact resolve eq1241486 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241486
  have eq1241838 : ∀ X0 : G, (k x (M.op (σ X0) x)) = (M.op (σ (M.op X0 x)) x) := by
    intro X0
    first
    | (have i₁ := eq1241508 X0
       have i₂ := eq1240159 (M.op X0 x)
       grind)
    | exact superpose eq1240159 eq1241508
    | exact resolve eq1241508 eq1240159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240159 eq1241508
  have eq1242035 : ∀ X0 : G, (σ (M.op x X0)) = (k x (M.op (σ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq1241838 X0
       have i₂ := eq1241062 x X0
       grind)
    | exact superpose eq1241062 eq1241838
    | exact resolve eq1241838 eq1241062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241062 eq1241838
  have eq1242161 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op (σ X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq1242035 X0
       have i₂ := eq1238802 (M.op (σ X0) x)
       grind)
    | exact superpose eq1238802 eq1242035
    | exact resolve eq1242035 eq1238802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238802 eq1242035
  have eq1242248 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1242161 X0
       have i₂ := eq65398 x (σ X0)
       grind)
    | exact superpose eq65398 eq1242161
    | exact resolve eq1242161 eq65398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65398 eq1242161
  have eq1246832 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq61750
       have i₂ := eq1242248 y
       grind)
    | exact superpose eq1242248 eq61750
    | (have r₁ := eq61750
       have r₂ := eq1242248 y
       grind)
    | exact resolve eq61750 eq1242248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61750 eq1242248
  have eq1247088 : False := by grind
  exact eq1247088

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1473 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1492 : False := by grind
  exact eq1492

/-- `Equation417`: `x = x ◇ (x ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation417 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law417 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1474 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1493 : False := by grind
  exact eq1493

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation418 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq426 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq432 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq426 (σ X0) (σ X1)
       grind)
    | exact superpose eq426 eq13
    | exact resolve eq13 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq426 X0 X1
       grind)
    | exact superpose eq426 eq432
    | exact resolve eq432 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq432
  have eq1184 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq445 x y
       grind)
    | exact superpose eq445 eq14
    | (have r₁ := eq14
       have r₂ := eq445 x y
       grind)
    | exact resolve eq14 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq1208 : False := by grind
  exact eq1208
