import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq67 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ X0) X1) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq96 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq25 X1 X0 x
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq40
    | (have j0 := eq40 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq40 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq41
    | (have j0 := eq41 X0 X1
       have j1 := eq40 X0 X1
       grind)
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq238 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq41
    | (have j0 := eq41 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X0)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq22
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq22 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq757 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq85 X1 X0
       grind)
    | exact superpose eq85 eq9
    | exact resolve eq9 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (M.op X0 x) X0 X1
       have i₂ := eq35 X0 X1 x
       grind)
    | exact superpose eq35 eq96
    | (have j1 := eq35 X0 X1 x
       grind)
    | exact resolve eq96 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1026 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq975 X0 X1
       have j1 := eq147 X1 X0
       grind)
    | (have r₁ := eq975 X0 X1
       have r₂ := eq147 X0 X1
       grind)
    | (have r₁ := eq975 X1 X0
       have r₂ := eq147 X0 X1
       grind)
    | (have r₁ := eq975 (M.op X1 X0) (M.op X0 X1)
       have r₂ := eq147 X0 X1
       grind)
    | exact resolve eq975 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1265 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op X0 (σ X1)) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (M.op X0 (σ X1))
       have i₂ := eq85 (σ X1) X0
       grind)
    | exact superpose eq85 eq67
    | exact resolve eq67 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq85
  have eq5322 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq21901 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq236 x y
       grind)
    | exact superpose eq236 eq16
    | (have j1 := eq236 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq236 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq236 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq236 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq22057 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by grind
  clear eq21901
  have eq23356 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq238 x y
       grind)
    | exact superpose eq238 eq16
    | (have j1 := eq238 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq238 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq238 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq238 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq23512 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq23356
  have eq23859 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq22057
       grind)
    | exact superpose eq22057 eq16
    | exact resolve eq16 eq22057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23902 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ y) (M.op (M.op X0 (σ x)) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq96 X0 (σ x) (σ y)
       have i₂ := eq22057
       grind)
    | exact superpose eq22057 eq96
    | exact resolve eq96 eq22057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq24013 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq23902 x
       have i₂ := eq1265 x x
       grind)
    | exact superpose eq1265 eq23902
    | exact resolve eq23902 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq23902
  have eq24241 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0) (σ X1)
       have i₂ := eq242 X0 X1
       grind)
    | exact superpose eq242 eq25
    | (have j1 := eq242 X0 X1
       grind)
    | exact resolve eq25 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq242
  have eq24520 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24241 X0 X1
       have i₂ := eq757 X0 X0
       grind)
    | exact superpose eq757 eq24241
    | (have j0 := eq24241 X0 X1
       grind)
    | exact resolve eq24241 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq24241
  have eq24649 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq24520 X0 X1
       have j1 := eq5322 X1 X0
       grind)
    | (have r₁ := eq24520 X0 X1
       have r₂ := eq5322 X0 X1
       grind)
    | (have r₁ := eq24520 X1 X0
       have r₂ := eq5322 X0 X1
       grind)
    | exact resolve eq24520 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322 eq24520
  have eq44333 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq23512
       grind)
    | exact superpose eq23512 eq16
    | exact resolve eq16 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23512
  have eq75152 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq147 (σ x) (σ y)
       have i₂ := eq24013
       grind)
    | exact superpose eq24013 eq147
    | (have j0 := eq147 (σ (M.op x x)) (k (σ x) (σ y))
       grind)
    | exact resolve eq147 eq24013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq75155 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq148 (σ y) (σ x)
       have i₂ := eq24013
       grind)
    | exact superpose eq24013 eq148
    | (have j0 := eq148 y x
       grind)
    | exact resolve eq148 eq24013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24013
  have eq75299 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by grind
  clear eq75155
  have eq75302 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by grind
  clear eq75152
  have eq75362 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq75299
       have r₂ := eq22057
       grind)
    | exact resolve eq75299 eq22057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75299
  have eq75364 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq75302
       have r₂ := eq22057
       grind)
    | exact resolve eq75302 eq22057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22057 eq75302
  have eq75386 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq75362
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq75362
    | exact resolve eq75362 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75362
  have eq75388 : (σ (M.op x x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq75364
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq75364
    | exact resolve eq75364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75364
  have eq97639 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq75386
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq75386
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq75386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75386
  have eq97794 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq97639
  have eq97808 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq97794
       have r₂ := eq44333
       grind)
    | exact resolve eq97794 eq44333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44333 eq97794
  have eq131878 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq148 x y
       have i₂ := eq97808
       grind)
    | exact superpose eq97808 eq148
    | (have j0 := eq148 x y
       grind)
    | (have r₁ := eq148 y x
       have r₂ := eq97808
       grind)
    | (have r₁ := eq148 x y
       have r₂ := eq97808
       grind)
    | exact resolve eq148 eq97808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq97808
  have eq132110 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq131878
  have eq132111 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq132110
  have eq191313 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq75388
       have i₂ := eq132111
       grind)
    | exact superpose eq132111 eq75388
    | exact resolve eq75388 eq132111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75388 eq132111
  have eq191487 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq191313
  have eq191501 : (σ x) = (σ y) ∨ (k y x) = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq191487
       have r₂ := eq23859
       grind)
    | exact resolve eq191487 eq23859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23859 eq191487
  have eq191503 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 (k y x) (M.op y x)
       grind)
    | (have r₁ := eq191501
       have r₂ := eq13 y x
       grind)
    | exact resolve eq191501 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191501
  have eq217514 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1026 x y
       have i₂ := eq191503
       grind)
    | exact superpose eq191503 eq1026
    | (have j0 := eq1026 (M.op x y) (M.op y x)
       grind)
    | exact resolve eq1026 eq191503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq217516 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24649 x y
       have i₂ := eq191503
       grind)
    | exact superpose eq191503 eq24649
    | (have j0 := eq24649 x y
       grind)
    | exact resolve eq24649 eq191503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24649 eq191503
  have eq217517 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq217516
  have eq217519 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq217514
  have eq291293 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq217517
       grind)
    | exact superpose eq217517 eq16
    | exact resolve eq16 eq217517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217517
  have eq322688 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq291293
       have i₂ := eq217519
       grind)
    | exact superpose eq217519 eq291293
    | exact resolve eq291293 eq217519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217519 eq291293
  have eq322702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq322688
  have eq322703 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq322702
  have eq354119 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq322703
       grind)
    | exact superpose eq322703 eq10
    | exact resolve eq10 eq322703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322703
  have eq354265 : x = y ∨ x = y := by
    first
    | (have i₁ := eq354119
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq354119
    | exact resolve eq354119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354119
  have eq354266 : x = y := by grind
  clear eq354265
  have eq378150 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq354266
       grind)
    | exact superpose eq354266 eq16
    | exact resolve eq16 eq354266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354266
  have eq378151 : False := by grind
  exact eq378151

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq554 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq537
    | (have j0 := eq537 X0 X1
       grind)
    | exact resolve eq537 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq537
  have eq599 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq554
    | exact resolve eq554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq629 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq634 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq629 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq629 X1 X0
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq629 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq629
  have eq637 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq634
    | exact resolve eq634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq688 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq637 X0 (τ X1)
       grind)
    | exact superpose eq637 eq18
    | (have j1 := eq637 X0 (τ X1)
       grind)
    | exact resolve eq18 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq798 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq688 X0 X1
       grind)
    | exact superpose eq688 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq688 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq688 X0 X1
       grind)
    | exact resolve eq13 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) X0
       have i₂ := eq688 X0 X1
       grind)
    | exact superpose eq688 eq12
    | (have j1 := eq688 X0 X1
       grind)
    | exact resolve eq12 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq812 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq798 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq821 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq812 X0 X1
       have j1 := eq800 X0 X1
       grind)
    | (have r₁ := eq812 X0 X1
       have r₂ := eq800 X0 X1
       grind)
    | exact resolve eq812 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq812
  have eq968 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq821 (τ X0) X1
       grind)
    | exact superpose eq821 eq19
    | (have j1 := eq821 (τ X0) X1
       grind)
    | exact resolve eq19 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq821
  have eq979 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq968 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq968
    | (have j0 := eq968 X0 X1
       grind)
    | exact resolve eq968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq990 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq979
    | (have j0 := eq979 X0 X1
       grind)
    | exact resolve eq979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq991 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq990 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq990
    | (have j0 := eq990 X0 X1
       grind)
    | exact resolve eq990 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1048 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq991 X0 X1
       have i₂ := eq637 X0 X1
       grind)
    | exact superpose eq637 eq991
    | (have j1 := eq637 X0 X1
       grind)
    | exact resolve eq991 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1090 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1048 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1212 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1090
    | (have j0 := eq1090 X1 (σ X0)
       grind)
    | exact resolve eq1090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1970 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq1212 X0 X1
       grind)
    | exact superpose eq1212 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq1212 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq1212 X0 X1
       grind)
    | exact resolve eq13 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1972 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq1212 X0 X1
       grind)
    | exact superpose eq1212 eq12
    | (have j1 := eq1212 X1 X0
       grind)
    | exact resolve eq12 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1977 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1212 y (σ x)
       grind)
    | exact superpose eq1212 eq16
    | (have j1 := eq1212 y (σ x)
       grind)
    | exact resolve eq16 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1985 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1970 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970
  have eq1992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq1977
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1977
    | exact resolve eq1977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq1996 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1985 X0 X1
       have j1 := eq1972 X0 X1
       grind)
    | (have r₁ := eq1985 X0 X1
       have r₂ := eq1972 X0 X1
       grind)
    | exact resolve eq1985 eq1972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972 eq1985
  have eq2012 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have r₁ := eq1992
       have r₂ := eq16
       grind)
    | exact resolve eq1992 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq2149 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq1996 (σ X0) X1
       grind)
    | exact superpose eq1996 eq23
    | (have j1 := eq1996 (σ X0) X1
       grind)
    | exact resolve eq23 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1996
  have eq2164 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2149 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2149
    | (have j0 := eq2149 X0 X1
       grind)
    | exact resolve eq2149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2177 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2164 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2164
    | (have j0 := eq2164 X0 X1
       grind)
    | exact resolve eq2164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2177 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2177
    | (have j0 := eq2177 X0 X1
       grind)
    | exact resolve eq2177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq2300 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2184 x y
       grind)
    | exact superpose eq2184 eq16
    | (have j1 := eq2184 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2184 x y
       grind)
    | exact resolve eq16 eq2184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184
  have eq2328 : x = (k y x) := by grind
  clear eq2300
  have eq2359 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq637 x y
       have i₂ := eq2328
       grind)
    | exact superpose eq2328 eq637
    | (have j0 := eq637 x y
       grind)
    | exact resolve eq637 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq2328
  have eq2362 : x = (M.op x y) := by grind
  clear eq2359
  have eq2413 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2012
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq2012
    | exact resolve eq2012 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012 eq2362
  have eq2425 : False := by grind
  exact eq2425

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation221 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq449 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq474 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq483 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq719 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq483 x y
       grind)
    | exact superpose eq483 eq16
    | (have j1 := eq483 x y
       grind)
    | exact resolve eq16 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq483 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq3424 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq474
    | exact resolve eq474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq3479 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3424 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3424
    | (have j0 := eq3424 X0 X1
       grind)
    | exact resolve eq3424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3424
  have eq6758 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq719
       have i₂ := eq3479 y x
       grind)
    | exact superpose eq3479 eq719
    | (have j1 := eq3479 y x
       grind)
    | (have r₁ := eq719
       have r₂ := eq3479 y x
       grind)
    | (have r₁ := eq719
       have r₂ := eq3479 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq719
       have r₂ := eq3479 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq719 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq3479
  have eq6759 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6758
  have eq6777 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 (τ X1) (τ X0)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq727
    | (have j0 := eq727 (τ X1) (τ X0)
       grind)
    | exact resolve eq727 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq6835 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6777 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq6777
    | (have j0 := eq6777 X0 X1
       grind)
    | exact resolve eq6777 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777
  have eq6870 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6835 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6835
    | (have j0 := eq6835 X0 X1
       grind)
    | exact resolve eq6835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6835
  have eq6902 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6870 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6870
    | (have j0 := eq6870 X0 X1
       grind)
    | exact resolve eq6870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6870
  have eq6928 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6902 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6902
    | (have j0 := eq6902 X0 X1
       grind)
    | exact resolve eq6902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6902
  have eq6948 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6928 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq6928
    | (have j0 := eq6928 X0 X1
       grind)
    | exact resolve eq6928 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6928
  have eq6967 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6948 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6948
    | (have j0 := eq6948 X0 X1
       grind)
    | exact resolve eq6948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6948
  have eq6980 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6967 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6967
    | (have j0 := eq6967 X0 X1
       grind)
    | exact resolve eq6967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6967
  have eq15421 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6759
       grind)
    | exact superpose eq6759 eq16
    | exact resolve eq16 eq6759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6759
  have eq15422 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15421
       have r₂ := eq23 x
       grind)
    | exact resolve eq15421 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15421
  have eq15424 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15422
       grind)
    | exact superpose eq15422 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15422
       grind)
    | exact resolve eq13 eq15422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15422
  have eq15427 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15424
  have eq17418 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15427
       grind)
    | exact superpose eq15427 eq16
    | exact resolve eq16 eq15427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15427
  have eq17419 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq17418
       have r₂ := eq23 x
       grind)
    | exact resolve eq17418 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17418
  have eq17423 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq449 x (σ y)
       have i₂ := eq17419
       grind)
    | exact superpose eq17419 eq449
    | (have j0 := eq449 x (σ y)
       grind)
    | (have r₁ := eq449 x (σ y)
       have r₂ := eq17419
       grind)
    | exact resolve eq449 eq17419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17419
  have eq17437 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq17423
  have eq17438 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq17437
  have eq17444 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17438
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17438
    | exact resolve eq17438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17438
  have eq17455 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq727 x y
       have i₂ := eq17444
       grind)
    | exact superpose eq17444 eq727
    | (have j0 := eq727 x y
       grind)
    | (have r₁ := eq727 x y
       have r₂ := eq17444
       grind)
    | exact resolve eq727 eq17444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17444
  have eq17483 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq17455
  have eq17484 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq17483
  have eq17489 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq727 x y
       grind)
    | (have r₁ := eq17484
       have r₂ := eq727 x y
       grind)
    | exact resolve eq17484 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq17484
  have eq17493 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17489
       grind)
    | exact superpose eq17489 eq16
    | exact resolve eq16 eq17489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17495 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq449 x (σ y)
       have i₂ := eq17489
       grind)
    | exact superpose eq17489 eq449
    | (have j0 := eq449 x (σ y)
       grind)
    | (have r₁ := eq449 x (σ y)
       have r₂ := eq17489
       grind)
    | exact resolve eq449 eq17489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq17489
  have eq17509 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq17495
  have eq17510 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq17509
  have eq17516 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17510
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17510
    | exact resolve eq17510 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17510
  have eq17524 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17516
       grind)
    | exact superpose eq17516 eq10
    | exact resolve eq10 eq17516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17516
  have eq17694 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17524
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17524
    | exact resolve eq17524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17524
  have eq17696 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17694
       grind)
    | exact superpose eq17694 eq16
    | exact resolve eq16 eq17694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17694
  have eq17697 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq17696
       have r₂ := eq23 x
       grind)
    | exact resolve eq17696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17696
  have eq17711 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq10
    | exact resolve eq10 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17697
  have eq17882 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq17711
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17711
    | exact resolve eq17711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17711
  have eq17912 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq6980 y x
       have i₂ := eq17882
       grind)
    | exact superpose eq17882 eq6980
    | (have j0 := eq6980 y x
       grind)
    | (have r₁ := eq6980 y x
       have r₂ := eq17882
       grind)
    | exact resolve eq6980 eq17882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980 eq17882
  have eq17917 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17912
  have eq17921 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17493
       have i₂ := eq17917
       grind)
    | exact superpose eq17917 eq17493
    | exact resolve eq17493 eq17917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17493 eq17917
  have eq17931 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17921
  have eq17932 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17931
       grind)
    | exact superpose eq17931 eq16
    | exact resolve eq16 eq17931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17931
  have eq17935 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17932
       have r₂ := eq23 x
       grind)
    | exact resolve eq17932 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17932
  have eq17936 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17935
       grind)
    | exact superpose eq17935 eq16
    | exact resolve eq16 eq17935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17937 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17935
       grind)
    | exact superpose eq17935 eq10
    | exact resolve eq10 eq17935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17935
  have eq18107 : x = y := by
    first
    | (have i₁ := eq17937
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17937
    | exact resolve eq17937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17937
  have eq18108 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17936
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq17936
    | exact resolve eq17936 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17936
  have eq18109 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18108
       have i₂ := eq18107
       grind)
    | exact superpose eq18107 eq18108
    | exact resolve eq18108 eq18107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18107 eq18108
  have eq18110 : False := by grind
  exact eq18110

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq461 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq653 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464 x y
       grind)
    | exact superpose eq464 eq16
    | (have j1 := eq464 y x
       grind)
    | exact resolve eq16 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq464 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3530 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq461 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq461
    | exact resolve eq461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq3596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3530 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3530
    | (have j0 := eq3530 X0 X1
       grind)
    | exact resolve eq3530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq7197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq653
       have i₂ := eq3596 x y
       grind)
    | exact superpose eq3596 eq653
    | (have j1 := eq3596 (σ x) (σ y)
       grind)
    | (have r₁ := eq653
       have r₂ := eq3596 x y
       grind)
    | (have r₁ := eq653
       have r₂ := eq3596 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq653
       have r₂ := eq3596 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq653 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq7198 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq7197
  have eq14437 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X1 X0
       have i₂ := eq464 X0 X1
       grind)
    | exact superpose eq464 eq660
    | (have j0 := eq660 X0 X1
       have j1 := eq464 X0 X1
       grind)
    | (have r₁ := eq660 X0 X0
       have r₂ := eq464 X0 X0
       grind)
    | exact resolve eq660 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq14438 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14437 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437
  have eq14439 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14438 X0 X1
       have j1 := eq660 X0 X1
       grind)
    | (have r₁ := eq14438 X0 X1
       have r₂ := eq660 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq14438 X0 X1
       have r₂ := eq660 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq14438 X1 X0
       have r₂ := eq660 X0 X1
       grind)
    | exact resolve eq14438 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq14438
  have eq14642 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14439 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq14439
    | (have j0 := eq14439 (τ X0) (τ X1)
       grind)
    | exact resolve eq14439 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq14710 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14642 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq14642
    | (have j0 := eq14642 X0 X1
       grind)
    | exact resolve eq14642 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq14642
  have eq14788 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14710 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14710
    | (have j0 := eq14710 X0 X1
       grind)
    | exact resolve eq14710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14710
  have eq14838 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14788 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq14788
    | (have j0 := eq14788 X0 X1
       grind)
    | (have r₁ := eq14788 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq14788 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14788
  have eq14886 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14838 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14838
    | (have j0 := eq14838 X0 X1
       grind)
    | exact resolve eq14838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14838
  have eq14931 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14886 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14886
    | (have j0 := eq14886 X0 X1
       grind)
    | exact resolve eq14886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14886
  have eq14961 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) ∨ X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14931 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14931
    | (have j0 := eq14931 X0 X1
       grind)
    | exact resolve eq14931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931
  have eq14979 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14961 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14961
    | (have j0 := eq14961 X0 X1
       grind)
    | exact resolve eq14961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14961
  have eq19794 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7198
       grind)
    | exact superpose eq7198 eq16
    | exact resolve eq16 eq7198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7198
  have eq19795 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19794
       have r₂ := eq22 x
       grind)
    | exact resolve eq19794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19794
  have eq19797 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19795
       grind)
    | exact superpose eq19795 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19795
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19795
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19795
       grind)
    | exact resolve eq13 eq19795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19795
  have eq19798 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19797
  have eq20124 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19798
       grind)
    | exact superpose eq19798 eq16
    | exact resolve eq16 eq19798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19798
  have eq20125 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq20124
       have r₂ := eq22 x
       grind)
    | exact resolve eq20124 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20124
  have eq20127 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq20125
       grind)
    | exact superpose eq20125 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20125
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20125
       grind)
    | exact resolve eq13 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20128 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20125
       grind)
    | exact superpose eq20125 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20125
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20125
       grind)
    | exact resolve eq13 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20125
  have eq20129 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20128
  have eq20130 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20129
  have eq20131 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20127
  have eq20132 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20131
  have eq20134 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq20130
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20130
    | exact resolve eq20130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20130
  have eq20135 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq20132
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20132
    | exact resolve eq20132 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20132
  have eq20164 : (σ (k y x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq20134
       have i₂ := eq20135
       grind)
    | exact superpose eq20135 eq20134
    | exact resolve eq20134 eq20135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20134 eq20135
  have eq20181 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq20164
  have eq20190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq653
       have i₂ := eq20181
       grind)
    | exact superpose eq20181 eq653
    | exact resolve eq653 eq20181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq20202 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq20190
  have eq20203 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq20202
  have eq20206 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq14439 x y
       grind)
    | (have r₁ := eq20203
       have r₂ := eq14439 y x
       grind)
    | (have r₁ := eq20203
       have r₂ := eq14439 x y
       grind)
    | exact resolve eq20203 eq14439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14439 eq20203
  have eq20216 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20206
       grind)
    | exact superpose eq20206 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20206
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20206
       grind)
    | exact resolve eq13 eq20206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20206
  have eq20217 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20216
  have eq20218 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20217
  have eq20222 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20218
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20218
    | exact resolve eq20218 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20218
  have eq20227 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20222
       grind)
    | exact superpose eq20222 eq16
    | exact resolve eq16 eq20222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20222
  have eq20252 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq20227
       have i₂ := eq20181
       grind)
    | exact superpose eq20181 eq20227
    | exact resolve eq20227 eq20181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20181
  have eq20257 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq20252
  have eq20258 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq20257
  have eq20260 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20258
       grind)
    | exact superpose eq20258 eq10
    | exact resolve eq10 eq20258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20258
  have eq20439 : x = y ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq20260
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20260
    | exact resolve eq20260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20260
  have eq20441 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20439
       grind)
    | exact superpose eq20439 eq16
    | exact resolve eq16 eq20439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20439
  have eq20442 : (σ (k y x)) = (σ (k x y)) := by
    first
    | (have r₁ := eq20441
       have r₂ := eq22 x
       grind)
    | exact resolve eq20441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20441
  have eq20446 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20227
       have i₂ := eq20442
       grind)
    | exact superpose eq20442 eq20227
    | exact resolve eq20227 eq20442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20227
  have eq20458 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq20442
       grind)
    | exact superpose eq20442 eq10
    | exact resolve eq10 eq20442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20442
  have eq20639 : (k y x) = (k x y) := by
    first
    | (have i₁ := eq20458
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq20458
    | exact resolve eq20458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20458
  have eq20674 : (k x y) ≠ (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq14979 x y
       have i₂ := eq20639
       grind)
    | exact superpose eq20639 eq14979
    | (have j0 := eq14979 x y
       grind)
    | (have r₁ := eq14979 y x
       have r₂ := eq20639
       grind)
    | (have r₁ := eq14979 x y
       have r₂ := eq20639
       grind)
    | exact resolve eq14979 eq20639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14979 eq20639
  have eq20686 : (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq20674
  have eq20693 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20686
       grind)
    | exact superpose eq20686 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20686
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20686
       grind)
    | exact resolve eq13 eq20686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20686
  have eq20697 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq20693
  have eq20698 : x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq20697
  have eq20700 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20698
       grind)
    | exact superpose eq20698 eq16
    | exact resolve eq16 eq20698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20698
  have eq20701 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq20700
       have r₂ := eq22 x
       grind)
    | exact resolve eq20700 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20700
  have eq22816 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20446
       have i₂ := eq20701
       grind)
    | exact superpose eq20701 eq20446
    | exact resolve eq20446 eq20701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20446 eq20701
  have eq22819 : (σ x) = (σ y) := by grind
  clear eq22816
  have eq22820 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22819
       grind)
    | exact superpose eq22819 eq16
    | exact resolve eq16 eq22819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22821 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22819
       grind)
    | exact superpose eq22819 eq10
    | exact resolve eq10 eq22819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22819
  have eq23000 : x = y := by
    first
    | (have i₁ := eq22821
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22821
    | exact resolve eq22821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22821
  have eq23001 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22820
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq22820
    | exact resolve eq22820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22820
  have eq23002 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23001
       have i₂ := eq23000
       grind)
    | exact superpose eq23000 eq23001
    | exact resolve eq23001 eq23000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23000 eq23001
  have eq23003 : False := by grind
  exact eq23003

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq35 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0)))
       have i₂ := eq9 X0 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq94 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq173 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq16
    | (have j1 := eq98 x y
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq182 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq173
    | (have j0 := eq173 X0 X1 X2
       grind)
    | exact resolve eq173 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq173
  have eq193 : ∀ X0 X1 X2 X3 : G, (σ (k (k (τ X0) X1) (k (τ X2) X3))) = (k (k X0 (σ X1)) (k X2 (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X2 X3 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq26
    | exact resolve eq26 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq571 : ∀ X0 X1 : G, (σ (M.op (M.op (k (τ X0) X1) (k (τ X0) X1)) (M.op (k (τ X0) X1) (k (τ X0) X1)))) = (M.op (M.op (k X0 (σ X1)) (k X0 (σ X1))) (M.op (k X0 (σ X1)) (k X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (k (τ X0) X1) (k (τ X0) X1))
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq22
    | exact resolve eq22 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq827 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (τ X4) (k (τ X5) (k (k (τ X0) X1) (k (τ X2) X3)))) = (τ (k X4 (k X5 (k (k X0 (σ X1)) (k X2 (σ X3)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq48 X5 (k (k (τ X0) X1) (k (τ X2) X3)) X4
       have i₂ := eq193 X0 X1 X2 X3
       grind)
    | exact superpose eq193 eq48
    | exact resolve eq48 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq193
  have eq932 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq978 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq932 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq932
    | (have j0 := eq932 X0 X1
       grind)
    | exact resolve eq932 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1399 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (M.op X0 (M.op X0 X0))) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ X0) = (k (σ (M.op (τ X1) (M.op X0 (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (M.op (τ X1) (M.op X0 (M.op X0 X0))) X1
       have i₂ := eq9 X0 (τ X1)
       grind)
    | exact superpose eq9 eq99
    | (have j0 := eq99 (M.op (τ X1) (M.op X0 (M.op X0 X0))) X1
       grind)
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1653 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq175
       have i₂ := eq978 x y
       grind)
    | exact superpose eq978 eq175
    | (have j1 := eq978 x y
       grind)
    | (have r₁ := eq175
       have r₂ := eq978 x y
       grind)
    | (have r₁ := eq175
       have r₂ := eq978 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq175
       have r₂ := eq978 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq175 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq978
  have eq1654 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1653
  have eq3784 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k X3 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq182 X0 X1 X2
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 (M.op (σ X0) (k (σ X1) X2)) (k X3 (k (σ X1) X2))
       have j1 := eq182 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq182 X0 X1 X2
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq20847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1654
       grind)
    | exact superpose eq1654 eq16
    | exact resolve eq16 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq20848 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20847
       have r₂ := eq22 x
       grind)
    | exact resolve eq20847 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20847
  have eq43503 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = X1 ∨ (τ (M.op X0 X0)) = X1 ∨ (σ X1) = (k (σ (M.op (τ X0) (M.op X1 (M.op X1 X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq1399 X1 X0
       grind)
    | exact superpose eq1399 eq9
    | (have j1 := eq1399 X1 X0
       grind)
    | exact resolve eq9 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq43507 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (τ (M.op X0 X0)) = X1 ∨ (σ X1) = (k (σ (M.op (τ X0) (M.op X1 (M.op X1 X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43503 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq43503
    | (have j0 := eq43503 X0 X1
       grind)
    | exact resolve eq43503 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43503
  have eq43508 : ∀ X0 X1 : G, (σ X1) = (k (σ (M.op (τ X0) (M.op X1 (M.op X1 X1)))) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43507 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43507
  have eq43562 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X1) (M.op (τ X0) (τ (M.op X0 X0))))) X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43508 X1 (τ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq43508
    | (have j0 := eq43508 X1 (τ X0)
       grind)
    | exact resolve eq43508 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq43678 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0))))) X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0)))) X1
       have i₂ := eq43508 (σ X1) X0
       grind)
    | exact superpose eq43508 eq28
    | (have j1 := eq43508 (σ X1) X0
       grind)
    | exact resolve eq28 eq43508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq43508
  have eq43871 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0))) X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43678 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq10 eq43678
    | (have j0 := eq43678 X0 X1
       grind)
    | exact resolve eq43678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43678
  have eq43947 : ∀ X0 X1 : G, (k (σ (M.op (τ X1) (M.op (τ X0) (τ (M.op X0 X0))))) X1) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43562 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43562
    | (have j0 := eq43562 X0 X1
       grind)
    | exact resolve eq43562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43562
  have eq44011 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 (M.op X0 (M.op X0 X0))) X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43871 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq43871
    | (have j0 := eq43871 X0 X1
       grind)
    | exact resolve eq43871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43871
  have eq44109 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X0 ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44011 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44011
    | (have j0 := eq44011 X0 X1
       grind)
    | exact resolve eq44011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44011
  have eq44170 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (k (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44109 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44109
    | (have j0 := eq44109 X0 X1
       grind)
    | exact resolve eq44109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44109
  have eq44213 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44170 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq44170
    | (have j0 := eq44170 X0 X1
       grind)
    | exact resolve eq44170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44170
  have eq301474 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3784 X0 X1 X2 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784
  have eq301475 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq301474 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301474
  have eq301480 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301475 X0 X1 X2
       have i₂ := eq35 X1 X2 X0
       grind)
    | exact superpose eq35 eq301475
    | (have j0 := eq301475 X0 X1 X2
       grind)
    | exact resolve eq301475 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq301475
  have eq301481 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq301480 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301480
  have eq302152 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq301481 (τ X0) X1 X2
       grind)
    | exact superpose eq301481 eq18
    | (have j1 := eq301481 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq301481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301481
  have eq302612 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302152 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302152
    | (have j0 := eq302152 X0 X1 X2
       grind)
    | exact resolve eq302152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302152
  have eq302831 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302612 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq302612
    | (have j0 := eq302612 X0 X1 X2
       grind)
    | exact resolve eq302612 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq302612
  have eq302989 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302831 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302831
    | (have j0 := eq302831 X0 X1 X2
       grind)
    | exact resolve eq302831 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302831
  have eq303284 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (k X0 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302989 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302989
    | exact resolve eq302989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303412 : ∀ X0 X1 X2 : G, (τ X0) = (τ (M.op X2 X2)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302989 X0 (M.op (τ X1) (M.op (τ X0) (τ (M.op X0 X0)))) X1
       have i₂ := eq43947 X0 X1
       grind)
    | exact superpose eq43947 eq302989
    | (have j1 := eq43947 X0 X2
       grind)
    | exact resolve eq302989 eq43947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43947 eq302989
  have eq305127 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq303284 (M.op X1 (M.op X0 (M.op X0 X0))) X1 X1
       have i₂ := eq44213 X0 X1
       grind)
    | exact superpose eq44213 eq303284
    | (have j0 := eq303284 X1 (M.op X1 X0) X0
       have j1 := eq44213 X0 X2
       grind)
    | exact resolve eq303284 eq44213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44213 eq303284
  have eq306905 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq305127 X1 (τ X0) X2
       grind)
    | exact superpose eq305127 eq18
    | (have j1 := eq305127 (k X0 (σ X1)) (σ (M.op (τ X0) X1)) X2
       grind)
    | exact resolve eq18 eq305127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq305127
  have eq312720 : ∀ X0 X1 X2 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ X1 = X2 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq303412 X1 X2 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq303412
    | (have j0 := eq303412 X1 X2 X2
       grind)
    | exact resolve eq303412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303412
  have eq313941 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq312720 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq312720
    | (have j0 := eq312720 X0 X1 X2
       grind)
    | exact resolve eq312720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312720
  have eq324108 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (τ (σ X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq313941 X2 (σ X1) (σ X0)
       grind)
    | exact superpose eq313941 eq15
    | (have j1 := eq313941 X0 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq313941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313941
  have eq324483 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324108 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq324108
    | (have j0 := eq324108 X0 X1 X2
       grind)
    | exact resolve eq324108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324108
  have eq407628 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq306905 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq306905
    | (have j0 := eq306905 X0 X1 X2
       grind)
    | exact resolve eq306905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306905
  have eq408276 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq407628 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq407628
    | (have j0 := eq407628 X0 X1 X2
       grind)
    | exact resolve eq407628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407628
  have eq652837 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq324483 x y X0
       grind)
    | exact superpose eq324483 eq16
    | (have j1 := eq324483 x y X0
       grind)
    | exact resolve eq16 eq324483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324483
  have eq653028 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq652837 X0
       have i₂ := eq408276 x y X1
       grind)
    | exact superpose eq408276 eq652837
    | (have j0 := eq652837 X0
       have j1 := eq408276 (M.op X0 X0) y X0
       grind)
    | (have r₁ := eq652837 X0
       have r₂ := eq408276 x y x
       grind)
    | (have r₁ := eq652837 X0
       have r₂ := eq408276 (σ (M.op x y)) (σ (k x y)) x
       grind)
    | (have r₁ := eq652837 X0
       have r₂ := eq408276 (σ (k x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq652837 eq408276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408276 eq652837
  have eq653045 : ∀ X0 X1 : G, x = y ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have j0 := eq653028 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653028
  have eq656334 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq653045 X0 X1
       grind)
    | exact superpose eq653045 eq16
    | (have j1 := eq653045 X0 X0
       grind)
    | exact resolve eq16 eq653045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653045
  have eq656335 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have j0 := eq656334 X0 X0
       grind)
    | (have r₁ := eq656334 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq656334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656334
  have eq656337 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq656335 X0 X1
       grind)
    | exact superpose eq656335 eq10
    | (have j1 := eq656335 X0 X0
       grind)
    | exact resolve eq10 eq656335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656335
  have eq656944 : ∀ X0 X1 : G, x = y ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq656337 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq656337
    | (have j0 := eq656337 X0 X0
       grind)
    | exact resolve eq656337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656337
  have eq659615 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq656944 X0 X1
       grind)
    | exact superpose eq656944 eq16
    | (have j1 := eq656944 X0 X0
       grind)
    | exact resolve eq16 eq656944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656944
  have eq659616 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have j0 := eq659615 X0 X0
       grind)
    | (have r₁ := eq659615 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq659615 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659615
  have eq660327 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq659616 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659616
  have eq660328 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq660327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660327
  have eq661426 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5))))) (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5)))))) (M.op (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5))))) (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5))))))) = (σ (M.op (M.op (τ (k X0 (k X1 (k (k X2 (σ X3)) (k X4 (σ X5)))))) (τ (k X0 (k X1 (k (k X2 (σ X3)) (k X4 (σ X5))))))) (M.op (τ (k X0 (k X1 (k (k X2 (σ X3)) (k X4 (σ X5)))))) (τ (k X0 (k X1 (k (k X2 (σ X3)) (k X4 (σ X5))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq571 X4 (k (τ X5) (k (k (τ X0) X1) (k (τ X2) X3)))
       have i₂ := eq827 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq827 eq571
    | exact resolve eq571 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq827
  have eq661910 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ y) = (M.op (M.op (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5))))) (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5)))))) (M.op (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5))))) (k X0 (σ (k (τ X1) (k (k (τ X2) X3) (k (τ X4) X5))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq661426 X0 X1 X2 X3 X4 X5
       have i₂ := eq660328 (M.op (τ (k X0 (k X1 (k (k X2 (σ X3)) (k X4 (σ X5)))))) (τ (k X0 (k X1 (k (k X2 (σ X3)) (k X4 (σ X5)))))))
       grind)
    | exact superpose eq660328 eq661426
    | exact resolve eq661426 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661426
  have eq662962 : y = (σ y) := by
    first
    | (have i₁ := eq661910 x x x x x x
       have i₂ := eq660328 (M.op (k x (σ (k (τ x) (k (k (τ x) x) (k (τ x) x))))) (k x (σ (k (τ x) (k (k (τ x) x) (k (τ x) x))))))
       grind)
    | exact superpose eq660328 eq661910
    | exact resolve eq661910 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661910
  have eq672793 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq660328 X1
       grind)
    | exact superpose eq660328 eq9
    | exact resolve eq9 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673174 : ∀ X0 : G, (M.op y (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq660328 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq660328 eq9
    | exact resolve eq9 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673363 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq42 X0 X0
       have i₂ := eq660328 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq660328 eq42
    | exact resolve eq42 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq673747 : ∀ X0 : G, (M.op y (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq673174 X0
       have i₂ := eq660328 X0
       grind)
    | exact superpose eq660328 eq673174
    | exact resolve eq673174 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673174
  have eq674109 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq672793 X0 X1
       have i₂ := eq673363 X1
       grind)
    | exact superpose eq673363 eq672793
    | exact resolve eq672793 eq673363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672793
  have eq674342 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq673747 X0
       have i₂ := eq673363 X0
       grind)
    | exact superpose eq673363 eq673747
    | exact resolve eq673747 eq673363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673747
  have eq697573 : (σ y) = (M.op (σ (M.op y y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq674109 (σ x) (σ y)
       have i₂ := eq20848
       grind)
    | exact superpose eq20848 eq674109
    | exact resolve eq674109 eq20848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20848 eq674109
  have eq698212 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq697573
       have i₂ := eq660328 y
       grind)
    | exact superpose eq660328 eq697573
    | exact resolve eq697573 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697573
  have eq698559 : y = (M.op y (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq698212
       have i₂ := eq662962
       grind)
    | exact superpose eq662962 eq698212
    | exact resolve eq698212 eq662962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698212
  have eq698779 : y = (σ x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq698559
       have i₂ := eq674342 (σ x)
       grind)
    | exact superpose eq674342 eq698559
    | exact resolve eq698559 eq674342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698559
  have eq698956 : y = (M.op x y) ∨ y = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq698779
       have i₂ := eq660328 y
       grind)
    | exact superpose eq660328 eq698779
    | exact resolve eq698779 eq660328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660328 eq698779
  have eq699040 : x = y ∨ y = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq698956
       have i₂ := eq673363 x
       grind)
    | exact superpose eq673363 eq698956
    | exact resolve eq698956 eq673363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698956
  have eq699088 : y = (σ x) ∨ x = y ∨ y = (σ x) := by
    first
    | (have i₁ := eq699040
       have i₂ := eq662962
       grind)
    | exact superpose eq662962 eq699040
    | exact resolve eq699040 eq662962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699040
  have eq699089 : x = y ∨ y = (σ x) := by grind
  clear eq699088
  have eq707303 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq699089
       grind)
    | exact superpose eq699089 eq16
    | exact resolve eq16 eq699089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699089
  have eq707311 : y = (σ x) := by
    first
    | (have r₁ := eq707303
       have r₂ := eq22 x
       grind)
    | exact resolve eq707303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq707303
  have eq707313 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq707311
       grind)
    | exact superpose eq707311 eq16
    | exact resolve eq16 eq707311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708242 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq707313
       have i₂ := eq674342 (σ y)
       grind)
    | exact superpose eq674342 eq707313
    | exact resolve eq707313 eq674342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674342 eq707313
  have eq708620 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq708242
       have i₂ := eq662962
       grind)
    | exact superpose eq662962 eq708242
    | exact resolve eq708242 eq662962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662962 eq708242
  have eq708918 : y ≠ (σ x) := by
    first
    | (have i₁ := eq708620
       have i₂ := eq673363 x
       grind)
    | exact superpose eq673363 eq708620
    | exact resolve eq708620 eq673363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673363 eq708620
  have eq709165 : False := by grind
  exact eq709165

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq95 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq222 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq93 x y
       grind)
    | exact superpose eq93 eq16
    | (have j1 := eq93 x y
       grind)
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq724 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq724
    | (have j0 := eq724 X0 X1
       grind)
    | exact resolve eq724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq875 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq225
    | (have j0 := eq225 (τ X0) (τ X1)
       grind)
    | exact resolve eq225 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq884 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq875 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq875
    | (have j0 := eq875 X0 X1
       grind)
    | exact resolve eq875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq887 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq884
    | (have j0 := eq884 X0 X1
       grind)
    | exact resolve eq884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq889 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq887
    | (have j0 := eq887 X0 X1
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq890 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq889 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq889
    | (have j0 := eq889 X0 X1
       grind)
    | exact resolve eq889 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq891 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq892 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq891 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq891
    | (have j0 := eq891 X0 X1
       grind)
    | exact resolve eq891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq222
       have i₂ := eq769 x y
       grind)
    | exact superpose eq769 eq222
    | (have j1 := eq769 (σ x) (σ y)
       grind)
    | (have r₁ := eq222
       have r₂ := eq769 x y
       grind)
    | (have r₁ := eq222
       have r₂ := eq769 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq222
       have r₂ := eq769 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq222 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq769
  have eq1036 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1035
  have eq6574 : y ≠ y ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1036
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1036
       grind)
    | exact resolve eq13 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq6575 : y ≠ y ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6574
  have eq6576 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6575
  have eq8776 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6576
       grind)
    | exact superpose eq6576 eq16
    | exact resolve eq16 eq6576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6576
  have eq8777 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq8776
       have r₂ := eq22 x
       grind)
    | exact resolve eq8776 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq8780 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq8777
       grind)
    | exact superpose eq8777 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8777
       grind)
    | exact resolve eq13 eq8777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8777
  have eq8781 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq8780
  have eq8782 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq8781
  have eq8784 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq8782
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8782
    | exact resolve eq8782 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8782
  have eq8900 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq225 x y
       have i₂ := eq8784
       grind)
    | exact superpose eq8784 eq225
    | (have j0 := eq225 x y
       grind)
    | (have r₁ := eq225 x y
       have r₂ := eq8784
       grind)
    | exact resolve eq225 eq8784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8784
  have eq8919 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq8900
  have eq8920 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq8919
  have eq8924 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq225 x y
       grind)
    | (have r₁ := eq8920
       have r₂ := eq225 x y
       grind)
    | exact resolve eq8920 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq8920
  have eq9116 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8924
       grind)
    | exact superpose eq8924 eq16
    | exact resolve eq16 eq8924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9117 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq8924
       grind)
    | exact superpose eq8924 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8924
       grind)
    | exact resolve eq13 eq8924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924
  have eq9118 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9117
  have eq9119 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9118
  have eq9121 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq9119
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9119
    | exact resolve eq9119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9119
  have eq9316 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9121
       grind)
    | exact superpose eq9121 eq10
    | exact resolve eq10 eq9121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9121
  have eq9402 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq9316
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9316
    | exact resolve eq9316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9316
  have eq9404 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9402
       grind)
    | exact superpose eq9402 eq16
    | exact resolve eq16 eq9402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9402
  have eq9405 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq9404
       have r₂ := eq22 x
       grind)
    | exact resolve eq9404 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9404
  have eq9582 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq9405
       grind)
    | exact superpose eq9405 eq10
    | exact resolve eq10 eq9405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9405
  have eq9671 : y = (k x y) := by
    first
    | (have i₁ := eq9582
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9582
    | exact resolve eq9582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9582
  have eq9683 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq892 x y
       have i₂ := eq9671
       grind)
    | exact superpose eq9671 eq892
    | (have j0 := eq892 x y
       grind)
    | (have r₁ := eq892 x y
       have r₂ := eq9671
       grind)
    | exact resolve eq892 eq9671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq9671
  have eq9695 : y = (M.op x y) ∨ x = y := by grind
  clear eq9683
  have eq9871 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9116
       have i₂ := eq9695
       grind)
    | exact superpose eq9695 eq9116
    | exact resolve eq9116 eq9695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9116 eq9695
  have eq9877 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq9871
  have eq9878 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9877
       grind)
    | exact superpose eq9877 eq16
    | exact resolve eq16 eq9877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9877
  have eq9883 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq9878
       have r₂ := eq22 x
       grind)
    | exact resolve eq9878 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9878
  have eq10093 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9883
       grind)
    | exact superpose eq9883 eq16
    | exact resolve eq16 eq9883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10094 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9883
       grind)
    | exact superpose eq9883 eq10
    | exact resolve eq10 eq9883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9883
  have eq10184 : x = y := by
    first
    | (have i₁ := eq10094
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10094
    | exact resolve eq10094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10094
  have eq10185 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10093
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq10093
    | exact resolve eq10093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10093
  have eq10186 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10185
       have i₂ := eq10184
       grind)
    | exact superpose eq10184 eq10185
    | exact resolve eq10185 eq10184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10184 eq10185
  have eq10187 : False := by grind
  exact eq10187

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pyx_y_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq73 : x ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq89 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq103 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq87
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq87 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq185 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq81 (σ X0) sF2
       grind)
    | exact superpose eq81 eq39
    | (have j1 := eq81 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq81
    | (have j0 := eq81 (σ y) (σ x)
       grind)
    | exact resolve eq81 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq191
    | exact resolve eq191 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq195 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq192
       have r₂ := eq27
       grind)
    | exact resolve eq192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq195
    | exact resolve eq195 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq199 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197 eq27
    | exact resolve eq27 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197 eq74
    | (have r₁ := eq74
       have r₂ := eq197
       grind)
    | exact resolve eq74 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq197
  have eq356 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq355
  have eq371 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq356 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq356
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq356
       grind)
    | exact resolve eq13 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1253 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq371 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq1256 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1253
    | exact resolve eq1253 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq1256
    | exact resolve eq1256 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1256
  have eq1270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1262
  have eq1273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1270
       have r₂ := eq199
       grind)
    | exact resolve eq1270 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq1270
  have eq1274 : x = (M.op x y) := by
    first
    | (have r₁ := eq1273
       have r₂ := eq27
       grind)
    | exact resolve eq1273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1280 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1274 eq20
    | exact resolve eq20 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1283 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | exact superpose eq1274 eq73
    | (have r₁ := eq73
       have r₂ := eq1274
       grind)
    | exact resolve eq73 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1289 : (M.op x x) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq1283
  have eq1295 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1280
    | exact resolve eq1280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1298 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1295 eq26
    | exact resolve eq26 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1397 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1289
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1289
       grind)
    | exact resolve eq13 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq3398 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1295 eq185
    | (have j0 := eq185 X0
       grind)
    | exact resolve eq185 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq3399 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1295 eq3398
    | (have j0 := eq3398 X0
       grind)
    | exact resolve eq3398 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq3588 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3399 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3399
    | (have j0 := eq3399 y
       grind)
    | exact resolve eq3399 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3399
  have eq3599 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1298 eq3588
    | exact resolve eq3588 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3588
  have eq3617 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3599
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq3599
    | exact resolve eq3599 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq3599
  have eq3630 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1295 eq3617
    | exact resolve eq3617 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617
  have eq3641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1298 eq3630
    | exact resolve eq3630 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq3630
  have eq3646 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3641
       have r₂ := eq27
       grind)
    | exact resolve eq3641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq3658 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3646 eq103
    | exact resolve eq103 eq3646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq3646
  have eq3660 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1274 eq3658
    | exact resolve eq3658 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3658
  have eq967845 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1397 X0
       have i₂ := eq3660
       grind)
    | exact superpose eq3660 eq1397
    | (have j0 := eq1397 X0
       grind)
    | exact resolve eq1397 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq967860 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq967845 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967845
  have eq967863 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq967860
       have i₂ := eq3660
       grind)
    | exact superpose eq3660 eq967860
    | exact resolve eq967860 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660 eq967860
  have eq967876 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq967863
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq967863
    | exact resolve eq967863 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq967863
  have eq967882 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1274 eq967876
    | exact resolve eq967876 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274 eq967876
  have eq967883 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq967882
  have eq967984 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq967883 eq15
    | exact resolve eq15 eq967883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967883
  have eq968637 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq967984
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq967984
    | exact resolve eq967984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq967984
  have eq968719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1295 eq968637
    | exact resolve eq968637 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq968637
  have eq968731 : False := by grind
  exact eq968731

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq273 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq275 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq289 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq290 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq301 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq290 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq290 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq303 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq273
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq306 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq303
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq303
    | exact resolve eq303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq449 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq301 X0 (τ X1)
       grind)
    | exact superpose eq301 eq17
    | (have j1 := eq301 X0 (τ X1)
       grind)
    | exact resolve eq17 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq455 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq301 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq449 (τ X0) X1
       grind)
    | exact superpose eq449 eq18
    | (have j1 := eq449 (τ X0) X1
       grind)
    | exact resolve eq18 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq449
  have eq702 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq697
    | (have j0 := eq697 X0 X1
       grind)
    | exact resolve eq697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq715 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq718 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq780 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq718
    | (have j0 := eq718 X1 (σ X0)
       grind)
    | exact resolve eq718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1248 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 X0
       have i₂ := eq301 X0 (σ X0)
       grind)
    | exact superpose eq301 eq780
    | (have j0 := eq780 X1 X0
       have j1 := eq301 X0 (σ X1)
       grind)
    | exact resolve eq780 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq780
  have eq1281 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1248 X0 X1
       have j1 := eq455 (σ X1) X0
       grind)
    | (have r₁ := eq1248 X1 X1
       have r₂ := eq455 (σ X1) X1
       grind)
    | exact resolve eq1248 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq1248
  have eq1514 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1281 (σ X0) X1
       grind)
    | exact superpose eq1281 eq22
    | (have j1 := eq1281 (σ X0) X1
       grind)
    | exact resolve eq22 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1281
  have eq1522 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1514 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1514
    | (have j0 := eq1514 X0 X1
       grind)
    | exact resolve eq1514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1538 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1522 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1522
    | (have j0 := eq1522 X0 X1
       grind)
    | exact resolve eq1522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1547 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1538 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1538
    | (have j0 := eq1538 X0 X1
       grind)
    | exact resolve eq1538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1547 x y
       grind)
    | exact superpose eq1547 eq16
    | (have j1 := eq1547 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1547 x y
       grind)
    | exact resolve eq16 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1670 : x = (k y x) := by grind
  clear eq1650
  have eq1920 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq306
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq306
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq306 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1921 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1920
  have eq1924 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1921
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1921 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1926 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1924
       have i₂ := eq1670
       grind)
    | exact superpose eq1670 eq1924
    | exact resolve eq1924 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq1927 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1926
       have i₂ := eq1670
       grind)
    | exact superpose eq1670 eq1926
    | exact resolve eq1926 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq1928 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq306
       have i₂ := eq1927
       grind)
    | exact superpose eq1927 eq306
    | exact resolve eq306 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq1927
  have eq1940 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1928
  have eq1941 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1940
       have i₂ := eq1670
       grind)
    | exact superpose eq1670 eq1940
    | exact resolve eq1940 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq1942 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1941
  have eq1944 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1942
       grind)
    | exact superpose eq1942 eq16
    | exact resolve eq16 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq1976 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1944
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1944
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1944 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1977 : x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1976
  have eq1981 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1977
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1977 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq1982 : x = (M.op x y) := by
    first
    | (have i₁ := eq1981
       have i₂ := eq1670
       grind)
    | exact superpose eq1670 eq1981
    | exact resolve eq1981 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670 eq1981
  have eq1983 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1944
       have i₂ := eq1982
       grind)
    | exact superpose eq1982 eq1944
    | exact resolve eq1944 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944 eq1982
  have eq1997 : False := by grind
  exact eq1997
