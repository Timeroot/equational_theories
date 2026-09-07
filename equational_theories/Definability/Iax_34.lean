import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation655`: `x = x ◇ (y ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation655 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law655 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law655.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) X2))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq15
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X2) X3)) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 (M.op (M.op X3 X2) X3)) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq8 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2) X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq73 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq48 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq129 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 x x (M.op X0 X0) X1
       have i₂ := eq21 X0 (M.op X0 X0) x x
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq162 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq129 X0 (M.op X0 X0)
       grind)
    | exact superpose eq129 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq129 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq233 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq168 X0 (τ X1)
       grind)
    | exact superpose eq168 eq16
    | exact resolve eq16 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq358 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq884 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq948 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq884
    | (have j0 := eq884 X0 X1
       grind)
    | exact resolve eq884 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq1614 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 X1 X1
       have i₂ := eq948 X0 X1
       grind)
    | exact superpose eq948 eq233
    | (have j1 := eq948 X2 X0
       grind)
    | exact resolve eq233 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq948
  have eq1880 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq358 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq358
    | (have j0 := eq358 (τ X0)
       grind)
    | exact resolve eq358 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq358
  have eq1898 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1880 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1880
    | (have j0 := eq1880 X0
       grind)
    | exact resolve eq1880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq1907 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1898 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1898
    | (have j0 := eq1898 X0
       grind)
    | exact resolve eq1898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq3029 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq73 x y X0
       grind)
    | exact superpose eq73 eq14
    | (have j1 := eq73 X0 y X0
       grind)
    | exact resolve eq14 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3102 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq3029 X0
       have j1 := eq1614 y X0 x
       grind)
    | (have r₁ := eq3029 X0
       have r₂ := eq1614 y x x
       grind)
    | exact resolve eq3029 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614 eq3029
  have eq3135 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1907 (σ y)
       have i₂ := eq3102 (σ y)
       grind)
    | exact superpose eq3102 eq1907
    | (have j0 := eq1907 (σ y)
       grind)
    | (have r₁ := eq1907 (σ y)
       have r₂ := eq3102 (σ y)
       grind)
    | exact resolve eq1907 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3151 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) X0
       have i₂ := eq3102 (σ X0)
       grind)
    | exact superpose eq3102 eq20
    | exact resolve eq20 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3102
  have eq3154 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3135
  have eq3155 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq3151 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3151
    | exact resolve eq3151 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3296 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1907 y
       have i₂ := eq3155 y
       grind)
    | exact superpose eq3155 eq1907
    | (have j0 := eq1907 y
       grind)
    | (have r₁ := eq1907 y
       have r₂ := eq3155 y
       grind)
    | exact resolve eq1907 eq3155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907 eq3155
  have eq3315 : y = (M.op y y) := by grind
  clear eq3296
  have eq3424 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq129 y X0
       have i₂ := eq3315
       grind)
    | exact superpose eq3315 eq129
    | exact resolve eq129 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq4996 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq129 (σ y) X0
       have i₂ := eq3154
       grind)
    | exact superpose eq3154 eq129
    | exact resolve eq129 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq3154
  have eq5243 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4996 (σ x)
       grind)
    | exact superpose eq4996 eq14
    | exact resolve eq14 eq4996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4996
  have eq5251 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5243
       have i₂ := eq3424 x
       grind)
    | exact superpose eq3424 eq5243
    | exact resolve eq5243 eq3424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3424 eq5243
  have eq5252 : False := by grind
  exact eq5252

/-- `Equation655`: `x = x ◇ (y ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxx_pxy_Equation655 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law655 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law655.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  clear eq15
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X2) X3)) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 (M.op (M.op X3 X2) X3)) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq20
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq32 X0 X1 X2
       grind)
    | exact superpose eq32 eq11
    | exact resolve eq11 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 (M.op X1 X1)) X0) (M.op X1 X1)
       have i₂ := eq21 X1 (M.op (M.op X0 (M.op X1 X1)) X0) (M.op X1 X1) X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq114 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (M.op X0 X0) x
       have i₂ := eq94 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq94 eq32
    | exact resolve eq32 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq94 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq94 eq8
    | exact resolve eq8 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq200 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X2 X1 (M.op X0 X0)
       have i₂ := eq115 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq115 eq32
    | exact resolve eq32 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq220 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq42 x y
       grind)
    | exact superpose eq42 eq14
    | (have j1 := eq42 x y
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq11 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq231 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       have j1 := eq11 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq224 X0 X1
       have r₂ := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq235 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq231
    | (have j0 := eq231 X0 X1
       grind)
    | exact resolve eq231 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq270 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq114 X1 (σ X0)
       grind)
    | exact superpose eq114 eq28
    | exact resolve eq28 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq114
  have eq2683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq220
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq220
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq220 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq2684 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2683
  have eq2798 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq235 (τ X1) (τ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq235
    | exact resolve eq235 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq235
  have eq2805 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2798 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2798
    | (have j0 := eq2798 X0 X1
       grind)
    | exact resolve eq2798 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798
  have eq2807 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2805 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2805
    | (have j0 := eq2805 X0 X1
       grind)
    | exact resolve eq2805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq2808 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2807 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2807
    | (have j0 := eq2807 X0 X1
       grind)
    | exact resolve eq2807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2807
  have eq2809 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2808 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2808
    | (have j0 := eq2808 X0 X1
       grind)
    | exact resolve eq2808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808
  have eq2997 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq2684
       grind)
    | exact superpose eq2684 eq8
    | exact resolve eq8 eq2684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq3021 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2997 X0
       have i₂ := eq115 (σ x) (σ y)
       grind)
    | exact superpose eq115 eq2997
    | exact resolve eq2997 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3317 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq270 y X0
       have i₂ := eq3021 (σ y)
       grind)
    | exact superpose eq3021 eq270
    | exact resolve eq270 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq3021
  have eq3325 : ∀ X0 : G, y = (k y (τ (M.op X0 X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3317 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3317
    | exact resolve eq3317 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq14710 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2809 y (τ (M.op x x))
       have i₂ := eq3325 x
       grind)
    | exact superpose eq3325 eq2809
    | (have r₁ := eq2809 y (τ (M.op x x))
       have r₂ := eq3325 x
       grind)
    | exact resolve eq2809 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809 eq3325
  have eq14719 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq14710
  have eq15640 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq115 y X0
       have i₂ := eq14719
       grind)
    | exact superpose eq14719 eq115
    | exact resolve eq115 eq14719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14719
  have eq16377 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq65 x X0 X0
       have i₂ := eq200 X0 X0 x
       grind)
    | exact superpose eq200 eq65
    | exact resolve eq65 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq200
  have eq16382 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16377 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq16377 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq16377 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16377
  have eq16623 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16382 (σ X0)
       grind)
    | exact superpose eq16382 eq13
    | exact resolve eq13 eq16382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16635 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16623 X0
       have i₂ := eq16382 X0
       grind)
    | exact superpose eq16382 eq16623
    | exact resolve eq16623 eq16382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16382 eq16623
  have eq19501 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ X0) X1
       have i₂ := eq16635 X0
       grind)
    | exact superpose eq16635 eq115
    | exact resolve eq115 eq16635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16635
  have eq21684 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq15640 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15640
  have eq21685 : x = (M.op x y) := by grind
  clear eq21684
  have eq22262 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq21685
       grind)
    | exact superpose eq21685 eq8
    | exact resolve eq8 eq21685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21685
  have eq22327 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22262 X0
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq22262
    | exact resolve eq22262 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq22262
  have eq23279 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19501 y X0
       have i₂ := eq22327 y
       grind)
    | exact superpose eq22327 eq19501
    | exact resolve eq19501 eq22327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19501
  have eq24894 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq23279 (σ x)
       grind)
    | exact superpose eq23279 eq14
    | exact resolve eq14 eq23279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23279
  have eq24914 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq24894
       have i₂ := eq22327 x
       grind)
    | exact superpose eq22327 eq24894
    | exact resolve eq24894 eq22327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22327 eq24894
  have eq24915 : False := by grind
  exact eq24915

/-- `Equation655`: `x = x ◇ (y ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyy_pxy_Equation655 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law655 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law655.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X2) X3)) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 (M.op (M.op X3 X2) X3)) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq8 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2) X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) = (M.op (M.op X1 (M.op (M.op X2 X1) X2)) (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) = (M.op (M.op X1 (M.op (M.op X2 X1) X2)) (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X2)) = (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1 X2
       have i₂ := eq8 (M.op X1 (M.op (M.op X2 X1) X2)) X1 X2
       grind)
    | exact superpose eq8 eq32
    | exact resolve eq32 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq20
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq97 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 x x (M.op X0 X0) X1
       have i₂ := eq21 X0 (M.op X0 X0) x x
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq125 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq11
    | (have j0 := eq11 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq137 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq97 X1 (M.op X1 X1)
       grind)
    | exact superpose eq97 eq133
    | exact resolve eq133 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq152 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op (M.op X1 X0) X1))) = (k X2 (σ (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq33 (τ X2) X0 X1
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq33
  have eq164 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq137 (σ X1) X0
       grind)
    | exact superpose eq137 eq28
    | exact resolve eq28 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq137
  have eq173 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq622 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq182
    | (have j0 := eq182 (τ X0) (τ X1)
       grind)
    | exact resolve eq182 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq182
  have eq629 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq633 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629
    | (have j0 := eq629 X0 X1
       grind)
    | exact resolve eq629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq636 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq637 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq636
    | (have j0 := eq636 X0 X1
       grind)
    | exact resolve eq636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq173
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq173
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq173 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq747 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq746
  have eq754 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq747
       grind)
    | exact superpose eq747 eq8
    | exact resolve eq8 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq756 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq754 X0
       have i₂ := eq97 (σ x) (σ y)
       grind)
    | exact superpose eq97 eq754
    | exact resolve eq754 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq796 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq164 (σ y) x
       have i₂ := eq756 (σ y)
       grind)
    | exact superpose eq756 eq164
    | exact resolve eq164 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq756
  have eq825 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq796 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq796
    | exact resolve eq796 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1008 : ∀ X0 : G, y ≠ X0 ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq637 X0 y
       have i₂ := eq825 X0
       grind)
    | exact superpose eq825 eq637
    | (have j0 := eq637 X0 y
       grind)
    | (have r₁ := eq637 y y
       have r₂ := eq825 y
       grind)
    | exact resolve eq637 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq2859 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1008 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq3256 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq97 y X0
       have i₂ := eq2859
       grind)
    | exact superpose eq2859 eq97
    | exact resolve eq97 eq2859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq3923 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq3256 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3924 : x = (M.op x y) := by grind
  clear eq3923
  have eq4504 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq8
    | exact resolve eq8 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4518 : ∀ X0 : G, (σ (M.op y (M.op x x))) = (k X0 (σ (M.op y (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq152 y x x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq152
    | exact resolve eq152 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq3924
  have eq4520 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4518 X0
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq4518
    | exact resolve eq4518 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518
  have eq4533 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4504 X0
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq4504
    | exact resolve eq4504 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq5581 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq637 X0 (σ y)
       have i₂ := eq4520 X0
       grind)
    | exact superpose eq4520 eq637
    | (have j0 := eq637 X0 (σ y)
       grind)
    | (have r₁ := eq637 (σ y) (σ y)
       have r₂ := eq4520 (σ y)
       grind)
    | exact resolve eq637 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq4520
  have eq7369 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq5581 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq7439 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 (σ y) X0
       have i₂ := eq7369
       grind)
    | exact superpose eq7369 eq97
    | exact resolve eq97 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq7369
  have eq7698 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq7439 (σ x)
       grind)
    | exact superpose eq7439 eq14
    | exact resolve eq14 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439
  have eq7702 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7698
       have i₂ := eq4533 x
       grind)
    | exact superpose eq4533 eq7698
    | exact resolve eq7698 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533 eq7698
  have eq7703 : False := by grind
  exact eq7703

/-- `Equation658`: `x = x ◇ (y ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation658 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law658 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law658.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq15
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq23 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq117 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq91 X0 (τ X1)
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1077 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1142 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1193 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X1 X1
       have i₂ := eq1142 X0 X1
       grind)
    | exact superpose eq1142 eq117
    | (have j1 := eq1142 X2 X0
       grind)
    | exact resolve eq117 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1142
  have eq2217 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (M.op X0 X0)
       have i₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq432
    | (have j0 := eq432 (M.op X0 X0)
       grind)
    | exact resolve eq432 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2231 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq432
    | (have j0 := eq432 (τ X0)
       grind)
    | exact resolve eq432 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq432
  have eq2244 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2231 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2231
    | (have j0 := eq2231 X0
       grind)
    | exact resolve eq2231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2260 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2251
    | (have j0 := eq2251 X0
       grind)
    | exact resolve eq2251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2732 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ (M.op X0 X0)) X1
       have i₂ := eq2244 X0
       grind)
    | exact superpose eq2244 eq72
    | exact resolve eq72 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq3041 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq103 x y X0
       grind)
    | exact superpose eq103 eq14
    | (have j1 := eq103 X0 y X0
       grind)
    | exact resolve eq14 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3123 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq3041 X0
       have j1 := eq1193 y X0 x
       grind)
    | (have r₁ := eq3041 X0
       have r₂ := eq1193 y x x
       grind)
    | exact resolve eq3041 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq3041
  have eq3173 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) X0
       have i₂ := eq3123 (σ X0)
       grind)
    | exact superpose eq3123 eq20
    | exact resolve eq20 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3123
  have eq3177 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq3173 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3173
    | exact resolve eq3173 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3309 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2260 y
       have i₂ := eq3177 y
       grind)
    | exact superpose eq3177 eq2260
    | (have j0 := eq2260 y
       grind)
    | (have r₁ := eq2260 y
       have r₂ := eq3177 y
       grind)
    | exact resolve eq2260 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260 eq3177
  have eq3329 : y = (M.op y y) := by grind
  clear eq3309
  have eq3447 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq3329
       grind)
    | exact superpose eq3329 eq72
    | exact resolve eq72 eq3329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3461 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2732 y X0
       have i₂ := eq3329
       grind)
    | exact superpose eq3329 eq2732
    | exact resolve eq2732 eq3329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq3329
  have eq4020 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3461 (σ x)
       grind)
    | exact superpose eq3461 eq14
    | exact resolve eq14 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461
  have eq4028 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4020
       have i₂ := eq3447 x
       grind)
    | exact superpose eq3447 eq4020
    | exact resolve eq4020 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447 eq4020
  have eq4029 : False := by grind
  exact eq4029

/-- `Equation658`: `x = x ◇ (y ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation658 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law658 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law658.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | exact resolve eq13 eq15
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq8 (M.op X0 (M.op (M.op X1 X1) X0)) X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X2 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X2) X1))
       have r₂ := eq8 (M.op X1 (M.op (M.op X2 X2) X1)) X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq20
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X2))) = X1 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X2 X1
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq23 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq79 : ∀ X0 X1 X3 : G, (M.op X1 X0) = X1 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq66 X0 X1 x X3
       have i₂ := eq72 x X0
       grind)
    | exact superpose eq72 eq66
    | (have j0 := eq66 X0 X1 x X3
       grind)
    | exact resolve eq66 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq95 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) = (k X0 (M.op X3 (M.op (M.op X4 X4) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq33 X3 X4 X0
       have i₂ := eq33 X1 X2 X0
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op (M.op X2 X2) X1)))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 (M.op (M.op X2 X2) X1))
       have i₂ := eq33 X1 X2 (τ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq136 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 X2 X0
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq91
    | exact resolve eq91 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 X2
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq72
    | exact resolve eq72 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (M.op X1 X1)
       have i₂ := eq91 X1 (σ X0)
       grind)
    | exact superpose eq91 eq29
    | exact resolve eq29 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq470 : ∀ X0 X1 X2 X3 : G, (k X2 (k X0 (M.op X1 X1))) = (k X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq136 X2 X3 (k X0 (M.op X1 X1))
       have i₂ := eq153 X0 X1 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq153 eq136
    | exact resolve eq136 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq718 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq46 X2 X0
       grind)
    | exact superpose eq46 eq72
    | (have j1 := eq46 X2 X0
       grind)
    | exact resolve eq72 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq799 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq79 (σ y) (σ x) X0
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 (σ y) x X0
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op X0 X0) X1
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq210
    | (have j0 := eq210 (M.op X0 X0) X1
       grind)
    | exact resolve eq210 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X1 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq210
    | exact resolve eq210 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq210 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1311 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1267 X0 X1
       have j1 := eq79 X1 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq1267 X0 X0
       have r₂ := eq79 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq1267 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1339 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1291 (σ X0)
       grind)
    | exact superpose eq1291 eq13
    | exact resolve eq13 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1341 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq1291 (τ X0)
       grind)
    | exact superpose eq1291 eq34
    | exact resolve eq34 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1344 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1341 X0
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq1341
    | exact resolve eq1341 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1346 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1339 X0
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq1339
    | exact resolve eq1339 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1498 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq1295 (τ X0) X1
       grind)
    | exact superpose eq1295 eq34
    | exact resolve eq34 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1295
  have eq1522 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1498 X0 X1
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq1498
    | exact resolve eq1498 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq1498
  have eq1603 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (τ X0) X1
       have i₂ := eq1344 X0
       grind)
    | exact superpose eq1344 eq72
    | exact resolve eq72 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1608 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq1344 X0
       grind)
    | exact superpose eq1344 eq91
    | exact resolve eq91 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2035 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq1346 X0
       grind)
    | exact superpose eq1346 eq72
    | exact resolve eq72 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2040 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) X1
       have i₂ := eq1346 X0
       grind)
    | exact superpose eq1346 eq91
    | exact resolve eq91 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1346
  have eq2077 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq2196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2077 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2077
    | (have j0 := eq2077 X0 X1
       grind)
    | exact resolve eq2077 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq4679 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X1)
       have i₂ := eq2040 X1 (σ X0)
       grind)
    | exact superpose eq2040 eq13
    | exact resolve eq13 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq6544 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X2 X2) X1))
       have i₂ := eq123 (σ X0) X1 X2
       grind)
    | exact superpose eq123 eq13
    | exact resolve eq13 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq6596 : ∀ X0 X1 X2 : G, (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) = (σ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6544 X0 X1 X2
       have i₂ := eq1344 (σ X0)
       grind)
    | exact superpose eq1344 eq6544
    | exact resolve eq6544 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344 eq6544
  have eq6722 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6596 X0 X1 X2
       have i₂ := eq10 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq10 eq6596
    | exact resolve eq6596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6596
  have eq7950 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3) = (k (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1311 X2 X1
       have i₂ := eq33 X0 X1 X2
       grind)
    | exact superpose eq33 eq1311
    | exact resolve eq1311 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq128321 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2035 X0 X1
       have i₂ := eq2196 X2 X0
       grind)
    | exact superpose eq2196 eq2035
    | (have j1 := eq2196 X2 X0
       grind)
    | exact resolve eq2035 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq2196
  have eq153553 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq718 y X0 x
       grind)
    | exact superpose eq718 eq14
    | (have j1 := eq718 y X0 x
       grind)
    | exact resolve eq14 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq154068 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq153553 X0
       have j1 := eq128321 y X0 x
       grind)
    | (have r₁ := eq153553 X0
       have r₂ := eq128321 y x x
       grind)
    | exact resolve eq153553 eq128321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128321 eq153553
  have eq154527 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (σ y) X1
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq136
    | exact resolve eq136 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq154535 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq160 X0 (σ y)
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq160
    | exact resolve eq160 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq154585 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1522 X0 (σ y)
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq1522
    | exact resolve eq1522 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq154590 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1603 (σ y) X0
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq1603
    | exact resolve eq1603 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq154591 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1608 (σ y) X0
       have i₂ := eq154068 (σ y)
       grind)
    | exact superpose eq154068 eq1608
    | exact resolve eq1608 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq154693 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op X2 (M.op (M.op X3 X3) X2))) = (k X1 (M.op (σ y) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 X1 X2 X3 (σ y) X0
       have i₂ := eq154068 (M.op X0 X0)
       grind)
    | exact superpose eq154068 eq95
    | exact resolve eq95 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq154757 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq154068 (σ x)
       grind)
    | exact superpose eq154068 eq14
    | exact resolve eq14 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154865 : ∀ X1 X2 X3 : G, (k X1 (M.op X2 (M.op (M.op X3 X3) X2))) = (k X1 (σ y)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq154693 x X1 X2 X3
       have i₂ := eq72 x (σ y)
       grind)
    | exact superpose eq72 eq154693
    | exact resolve eq154693 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq154693
  have eq154910 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq154591 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq154591
    | exact resolve eq154591 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154591
  have eq154911 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq154590 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq154590
    | exact resolve eq154590 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154590
  have eq154932 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq154535 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq154535
    | exact resolve eq154535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154535
  have eq154990 : ∀ X0 : G, (k X0 y) = (k (τ (σ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq154932 X0
       have i₂ := eq154585 (σ X0)
       grind)
    | exact superpose eq154585 eq154932
    | exact resolve eq154932 eq154585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154585 eq154932
  have eq155007 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq154990 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq154990
    | exact resolve eq154990 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154990
  have eq155077 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (k X0 (k X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq470 X1 y X0 X2
       have i₂ := eq154911 y
       grind)
    | exact superpose eq154911 eq470
    | exact resolve eq470 eq154911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq155174 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq4679 X0 y
       have i₂ := eq154911 y
       grind)
    | exact superpose eq154911 eq4679
    | exact resolve eq4679 eq154911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq155292 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq154911 x
       grind)
    | exact superpose eq154911 eq799
    | (have j0 := eq799 X0
       grind)
    | exact resolve eq799 eq154911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq154911
  have eq155293 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq155292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155292
  have eq155298 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq155293 X0
       have i₂ := eq154068 X0
       grind)
    | exact superpose eq154068 eq155293
    | exact resolve eq155293 eq154068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154068 eq155293
  have eq155369 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq155174 X0
       have i₂ := eq154910 (σ X0)
       grind)
    | exact superpose eq154910 eq155174
    | exact resolve eq155174 eq154910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155174
  have eq155389 : ∀ X0 X1 : G, (k X0 (σ y)) = (k X0 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq155077 X0 X1 x
       have i₂ := eq154527 X0 x
       grind)
    | exact superpose eq154527 eq155077
    | exact resolve eq155077 eq154527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154527 eq155077
  have eq155444 : ∀ X0 X1 : G, (k X0 y) = (k X0 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq155389 X0 X1
       have i₂ := eq155007 X0
       grind)
    | exact superpose eq155007 eq155389
    | exact resolve eq155389 eq155007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155389
  have eq158614 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (k X1 (k (τ X0) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 y X1
       have i₂ := eq155298 X0
       grind)
    | exact superpose eq155298 eq18
    | exact resolve eq18 eq155298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq158705 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq155298 (σ X0)
       grind)
    | exact superpose eq155298 eq13
    | exact resolve eq13 eq155298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158708 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ y)
       have i₂ := eq155298 (σ X0)
       grind)
    | exact superpose eq155298 eq29
    | exact resolve eq29 eq155298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq155298
  have eq158738 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq158708 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq158708
    | exact resolve eq158708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158708
  have eq158758 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq158614 X0 X1
       have i₂ := eq155444 X1 (τ X0)
       grind)
    | exact superpose eq155444 eq158614
    | exact resolve eq158614 eq155444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155444 eq158614
  have eq158774 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq158738 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq158738
    | exact resolve eq158738 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158738
  have eq158781 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq158758 X0 X1
       have i₂ := eq158705 X1
       grind)
    | exact superpose eq158705 eq158758
    | exact resolve eq158758 eq158705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158758
  have eq159995 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X3) ≠ (σ (k X0 (M.op X1 (M.op (M.op X2 X2) X1)))) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq210 (σ X0) X3
       have i₂ := eq6722 X0 X1 X2
       grind)
    | exact superpose eq6722 eq210
    | (have j0 := eq210 (σ X0) X3
       grind)
    | exact resolve eq210 eq6722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq160176 : ∀ X0 X1 X2 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (k (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3
       have i₂ := eq6722 X0 X1 X2
       grind)
    | exact superpose eq6722 eq13
    | exact resolve eq13 eq6722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq160287 : ∀ X0 X1 X2 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op (k X0 (M.op X1 (M.op (M.op X2 X2) X1))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq160176 X0 X1 X2 X3
       have i₂ := eq7950 X0 X1 X2 X3
       grind)
    | exact superpose eq7950 eq160176
    | exact resolve eq160176 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7950 eq160176
  have eq160428 : ∀ X0 X3 : G, (M.op (σ X0) X3) ≠ (σ (k X0 (σ y))) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq159995 X0 x x X3
       have i₂ := eq154865 X0 x x
       grind)
    | exact superpose eq154865 eq159995
    | (have j0 := eq159995 X0 x x X3
       grind)
    | exact resolve eq159995 eq154865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159995
  have eq160959 : ∀ X0 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op (k X0 (σ y)) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq160287 X0 x x X3
       have i₂ := eq154865 X0 x x
       grind)
    | exact superpose eq154865 eq160287
    | exact resolve eq160287 eq154865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154865 eq160287
  have eq161040 : ∀ X0 X3 : G, (M.op (σ X0) X3) ≠ (σ (k X0 y)) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq160428 X0 X3
       have i₂ := eq155007 X0
       grind)
    | exact superpose eq155007 eq160428
    | (have j0 := eq160428 X0 X3
       grind)
    | exact resolve eq160428 eq155007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160428
  have eq161451 : ∀ X0 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op (k X0 y) X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq160959 X0 X3
       have i₂ := eq155007 X0
       grind)
    | exact superpose eq155007 eq160959
    | exact resolve eq160959 eq155007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155007 eq160959
  have eq161526 : ∀ X0 X3 : G, (σ X0) ≠ (M.op (σ X0) X3) ∨ (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq161040 X0 X3
       have i₂ := eq158705 X0
       grind)
    | exact superpose eq158705 eq161040
    | (have j0 := eq161040 X0 X3
       grind)
    | exact resolve eq161040 eq158705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161040
  have eq161858 : ∀ X0 X3 : G, (k (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq161451 X0 X3
       have i₂ := eq158774 X0
       grind)
    | exact superpose eq158774 eq161451
    | exact resolve eq161451 eq158774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158774 eq161451
  have eq161882 : ∀ X0 X3 : G, (M.op (σ X0) X3) = (k (σ X0) X3) := by
    intro X0 X3
    first
    | (have j0 := eq161526 X0 X3
       have j1 := eq79 X3 x (σ X0)
       grind)
    | (have r₁ := eq161526 X0 X0
       have r₂ := eq79 X0 (σ X0) X3
       grind)
    | exact resolve eq161526 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq161526
  have eq162085 : ∀ X0 X3 : G, (M.op (M.op (σ X0) (σ X0)) (σ X3)) = (σ (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq161858 X0 X3
       have i₂ := eq1311 (σ X0) (σ X3)
       grind)
    | exact superpose eq1311 eq161858
    | exact resolve eq161858 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311 eq161858
  have eq162101 : ∀ X0 X3 : G, (σ X0) = (M.op (σ X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq161882 X0 X3
       have i₂ := eq158781 X3 X0
       grind)
    | exact superpose eq158781 eq161882
    | exact resolve eq161882 eq158781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158781 eq161882
  have eq162197 : ∀ X0 X3 : G, (σ (M.op X0 X3)) = (M.op (k (σ X0) y) (σ X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq162085 X0 X3
       have i₂ := eq154910 (σ X0)
       grind)
    | exact superpose eq154910 eq162085
    | exact resolve eq162085 eq154910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154910 eq162085
  have eq162266 : ∀ X0 X3 : G, (σ (M.op X0 X3)) = (M.op (σ (k X0 y)) (σ X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq162197 X0 X3
       have i₂ := eq155369 X0
       grind)
    | exact superpose eq155369 eq162197
    | exact resolve eq162197 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155369 eq162197
  have eq162310 : ∀ X0 X3 : G, (σ (M.op X0 X3)) = (σ (k X0 y)) := by
    intro X0 X3
    first
    | (have i₁ := eq162266 X0 X3
       have i₂ := eq162101 (k X0 y) (σ X3)
       grind)
    | exact superpose eq162101 eq162266
    | exact resolve eq162266 eq162101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162101 eq162266
  have eq162325 : ∀ X0 X3 : G, (σ X0) = (σ (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq162310 X0 X3
       have i₂ := eq158705 X0
       grind)
    | exact superpose eq158705 eq162310
    | exact resolve eq162310 eq158705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158705 eq162310
  have eq178933 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq154757
       have i₂ := eq162325 x y
       grind)
    | exact superpose eq162325 eq154757
    | (have r₁ := eq154757
       have r₂ := eq162325 x y
       grind)
    | exact resolve eq154757 eq162325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154757 eq162325
  have eq178934 : False := by grind
  exact eq178934

/-- `Equation658`: `x = x ◇ (y ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation658 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law658 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law658.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq23 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq118 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq91 X0 (τ X1)
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq432 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1077 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1194 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X1 X1
       have i₂ := eq1142 X0 X1
       grind)
    | exact superpose eq1142 eq118
    | (have j1 := eq1142 X2 X0
       grind)
    | exact resolve eq118 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1142
  have eq2216 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (M.op X0 X0)
       have i₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq432
    | (have j0 := eq432 (M.op X0 X0)
       grind)
    | exact resolve eq432 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2231 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq432
    | (have j0 := eq432 (τ X0)
       grind)
    | exact resolve eq432 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq432
  have eq2245 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq2251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2231 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2231
    | (have j0 := eq2231 X0
       grind)
    | exact resolve eq2231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2260 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2251
    | (have j0 := eq2251 X0
       grind)
    | exact resolve eq2251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2732 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ (M.op X0 X0)) X1
       have i₂ := eq2245 X0
       grind)
    | exact superpose eq2245 eq72
    | exact resolve eq72 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq3039 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq103 x y X0
       grind)
    | exact superpose eq103 eq14
    | (have j1 := eq103 X0 y X0
       grind)
    | exact resolve eq14 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3121 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq3039 X0
       have j1 := eq1194 y X0 x
       grind)
    | (have r₁ := eq3039 X0
       have r₂ := eq1194 y x x
       grind)
    | exact resolve eq3039 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq3039
  have eq3169 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ y)
       have i₂ := eq3121 (σ X0)
       grind)
    | exact superpose eq3121 eq29
    | exact resolve eq29 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3121
  have eq3175 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq3169 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3169
    | exact resolve eq3169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3307 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2260 y
       have i₂ := eq3175 y
       grind)
    | exact superpose eq3175 eq2260
    | (have j0 := eq2260 y
       grind)
    | (have r₁ := eq2260 y
       have r₂ := eq3175 y
       grind)
    | exact resolve eq2260 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260 eq3175
  have eq3327 : y = (M.op y y) := by grind
  clear eq3307
  have eq3443 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq72
    | exact resolve eq72 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3457 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2732 y X0
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq2732
    | exact resolve eq2732 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq3327
  have eq4016 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3457 (σ x)
       grind)
    | exact superpose eq3457 eq14
    | exact resolve eq14 eq3457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3457
  have eq4024 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4016
       have i₂ := eq3443 x
       grind)
    | exact superpose eq3443 eq4016
    | exact resolve eq4016 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443 eq4016
  have eq4025 : False := by grind
  exact eq4025

/-- `Equation677`: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation677 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law677 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law677.models_iff G M).mp hM
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
  have eq1497 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1517 : False := by grind
  exact eq1517

/-- `Equation692`: `x = y ◇ (x ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation692 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law692 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law692.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq22 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op (M.op X0 X1) X0)
       have i₂ := eq8 (M.op (M.op (M.op X0 X1) X0) X2) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq13
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq125 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq129 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq125 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq125 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq129 (σ X0) (σ X1)
       grind)
    | exact superpose eq129 eq13
    | exact resolve eq13 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq148
    | exact resolve eq148 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq428 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq428
       have i₂ := eq129 x y
       grind)
    | exact superpose eq129 eq428
    | exact resolve eq428 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq428
  have eq452 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq451
  have eq497 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq452
       have i₂ := eq157 x y
       grind)
    | exact superpose eq157 eq452
    | exact resolve eq452 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq452
  have eq603 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq497
       grind)
    | exact superpose eq497 eq9
    | exact resolve eq9 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq622 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq603
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq603
    | exact resolve eq603 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq755 : ∀ X0 : G, y = (M.op X0 (M.op (M.op (M.op x x) x) X0)) := by
    intro X0
    first
    | (have i₁ := eq22 x y X0
       have i₂ := eq622
       grind)
    | exact superpose eq622 eq22
    | exact resolve eq22 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq758 : x = y := by
    first
    | (have i₁ := eq755 x
       have i₂ := eq22 x x x
       grind)
    | exact superpose eq22 eq755
    | exact resolve eq755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq755
  have eq795 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq758
       grind)
    | exact superpose eq758 eq14
    | exact resolve eq14 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq796 : False := by grind
  exact eq796
