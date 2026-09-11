import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq48 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq96 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq354 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq9
    | (have j1 := eq95 X1 X0
       grind)
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq720 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq754 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq1242 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq354
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq354
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq354
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq354
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq354 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq1243 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1242
  have eq3876 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq3909 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3876 X0 X1
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq3876
    | (have j0 := eq3876 X0 X1
       grind)
    | exact resolve eq3876 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876
  have eq3915 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (τ (k X0 X1))) = (τ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3909 (τ X0) (τ X1)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq3909
    | (have j0 := eq3909 (τ X0) (τ X1)
       grind)
    | exact resolve eq3909 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909
  have eq8543 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1243
       grind)
    | exact superpose eq1243 eq16
    | exact resolve eq16 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq8544 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8543
       have r₂ := eq22 x
       grind)
    | exact resolve eq8543 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8543
  have eq8546 : x ≠ x ∨ (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8544
       grind)
    | exact superpose eq8544 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8544
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8544
       grind)
    | exact resolve eq13 eq8544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8549 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 y X0 x
       have i₂ := eq8544
       grind)
    | exact superpose eq8544 eq44
    | exact resolve eq44 eq8544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8544
  have eq8560 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8546
  have eq20687 : ∀ X0 X1 X2 X3 : G, (σ x) = (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X1 (σ y) X0 (σ x)
       have i₂ := eq8549 X2 X3
       grind)
    | exact superpose eq8549 eq44
    | (have j1 := eq8549 X2 X3
       grind)
    | exact resolve eq44 eq8549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8549
  have eq28858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8560
       grind)
    | exact superpose eq8560 eq16
    | exact resolve eq16 eq8560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8560
  have eq28859 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28858
       have r₂ := eq22 x
       grind)
    | exact resolve eq28858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28858
  have eq28864 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq362 y x X0
       have i₂ := eq28859
       grind)
    | exact superpose eq28859 eq362
    | (have j0 := eq362 y x x
       grind)
    | exact resolve eq362 eq28859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq28859
  have eq28892 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq28864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28864
  have eq28895 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28892 X0
       have i₂ := eq48 x X0
       grind)
    | exact superpose eq48 eq28892
    | exact resolve eq28892 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq28892
  have eq29322 : ∀ X0 X1 X2 : G, (σ x) = (σ y) ∨ (M.op X2 (σ y)) = (M.op X2 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X1 (σ y) X0 (σ x)
       have i₂ := eq28895 X2
       grind)
    | exact superpose eq28895 eq44
    | (have j1 := eq28895 X2
       grind)
    | exact resolve eq44 eq28895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139712 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X1) (τ X0)) ∨ (τ X0) = (τ X1) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq3915 X1 X0
       grind)
    | exact superpose eq3915 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq3915 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq3915 X0 X1
       grind)
    | exact resolve eq13 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq139746 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X1) (τ X0)) ∨ (τ X0) = (τ X1) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq139712 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139712
  have eq139747 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (k (τ X1) (τ X0)) ∨ (τ X0) = (τ X1) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq139746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139746
  have eq139756 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ X1) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq139747 X0 X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq139747
    | (have j0 := eq139747 X0 X1
       grind)
    | exact resolve eq139747 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq139747
  have eq139807 : ∀ X0 X1 : G, (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq139756 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq139756
    | (have j0 := eq139756 X0 X1
       grind)
    | exact resolve eq139756 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq139756
  have eq174680 : ∀ X0 X1 X2 X3 : G, y = (τ (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 y
       have i₂ := eq20687 X0 X1 X2 X3
       grind)
    | exact superpose eq20687 eq10
    | (have j1 := eq20687 X0 X1 X2 X3
       grind)
    | exact resolve eq10 eq20687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20687
  have eq174938 : ∀ X0 X1 X2 X3 : G, x = y ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq174680 X0 X1 X2 X3
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq174680
    | (have j0 := eq174680 X0 X1 X2 X3
       grind)
    | exact resolve eq174680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174680
  have eq174940 : ∀ X0 X1 X2 X3 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16
       have i₂ := eq174938 X0 X1 X2 X3
       grind)
    | exact superpose eq174938 eq16
    | (have j1 := eq174938 X0 X1 X2 X3
       grind)
    | exact resolve eq16 eq174938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174938
  have eq174977 : ∀ X0 X1 X2 X3 : G, (M.op X2 y) = (M.op X2 (M.op x X3)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq174940 X0 X1 X2 X3
       grind)
    | (have r₁ := eq174940 X0 X1 X2 X3
       have r₂ := eq22 x
       grind)
    | exact resolve eq174940 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174940
  have eq235818 : ∀ X0 X1 X2 : G, y = (τ (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 y
       have i₂ := eq29322 X1 X2 X0
       grind)
    | exact superpose eq29322 eq10
    | (have j1 := eq29322 X1 X2 X0
       grind)
    | exact resolve eq10 eq29322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29322
  have eq236095 : ∀ X0 X1 X2 : G, x = y ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq235818 X0 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq235818
    | (have j0 := eq235818 X0 X1 X2
       grind)
    | exact resolve eq235818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235818
  have eq236097 : ∀ X0 X1 X2 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16
       have i₂ := eq236095 X0 X1 X2
       grind)
    | exact superpose eq236095 eq16
    | (have j1 := eq236095 X0 X1 X2
       grind)
    | exact resolve eq16 eq236095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236095
  have eq236136 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq236097 X0 X1 X2
       grind)
    | (have r₁ := eq236097 X0 X1 X2
       have r₂ := eq22 x
       grind)
    | exact resolve eq236097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236097
  have eq237645 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq236136 (σ x) X0 X1
       grind)
    | exact superpose eq236136 eq16
    | (have j1 := eq236136 X0 X0 X1
       grind)
    | exact resolve eq16 eq236136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236136
  have eq237746 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237645 X0 X1
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq237645
    | (have j0 := eq237645 X0 X1
       grind)
    | exact resolve eq237645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237645
  have eq327384 : ∀ X0 X1 : G, (τ (M.op X0 (τ X1))) = (τ (τ (k X1 (σ X0)))) ∨ (τ X1) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq139807 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139807
    | (have j0 := eq139807 (M.op X0 (τ X1)) (τ (k X1 (σ X0)))
       grind)
    | exact resolve eq139807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139807
  have eq327922 : ∀ X0 X1 : G, (τ (M.op X0 (τ X1))) = (τ (k (τ X1) X0)) ∨ (τ X1) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq327384 X0 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq327384
    | (have j0 := eq327384 X0 X1
       grind)
    | exact resolve eq327384 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327384
  have eq327951 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (τ (M.op X0 (τ X1))) = (τ (k (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327922 X0 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq327922
    | (have j0 := eq327922 X0 X1
       grind)
    | exact resolve eq327922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq327922
  have eq327969 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (τ (M.op X0 (τ X1))) = (τ (k (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327951 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq327951
    | (have j0 := eq327951 X0 X1
       grind)
    | exact resolve eq327951 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327951
  have eq327982 : ∀ X0 X1 : G, (τ (M.op X0 (τ X1))) = (τ (k (τ X1) X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327969 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq327969
    | (have j0 := eq327969 X0 X1
       grind)
    | exact resolve eq327969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327969
  have eq328011 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq327982 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327982
    | (have j0 := eq327982 (τ (M.op X1 X0)) (k X0 X1)
       grind)
    | exact resolve eq327982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327982
  have eq330570 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq328011 X1 X0
       grind)
    | exact superpose eq328011 eq11
    | (have j1 := eq328011 X1 X0
       grind)
    | exact resolve eq11 eq328011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328011
  have eq330905 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330570 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq330570
    | (have j0 := eq330570 X0 X1
       grind)
    | exact resolve eq330570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330570
  have eq331067 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq330905 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq330905
    | (have j0 := eq330905 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq330905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330905
  have eq332065 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq331067 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq331067
    | (have j0 := eq331067 X0 X1
       grind)
    | exact resolve eq331067 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331067
  have eq377371 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq332065 y x
       grind)
    | exact superpose eq332065 eq16
    | (have j1 := eq332065 y x
       grind)
    | exact resolve eq16 eq332065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332065
  have eq378111 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq377371
       have i₂ := eq754 y x
       grind)
    | exact superpose eq754 eq377371
    | (have j1 := eq754 y x
       grind)
    | (have r₁ := eq377371
       have r₂ := eq754 y x
       grind)
    | (have r₁ := eq377371
       have r₂ := eq754 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq377371
       have r₂ := eq754 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq377371 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq377371
  have eq378112 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq378111
  have eq379135 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X2)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174977 X1 X2 X0 y
       have i₂ := eq378112
       grind)
    | exact superpose eq378112 eq174977
    | (have j0 := eq174977 X1 X2 X2 x
       grind)
    | exact resolve eq174977 eq378112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174977
  have eq379140 : ∀ X0 X1 : G, x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 y X0 x
       have i₂ := eq378112
       grind)
    | exact superpose eq378112 eq44
    | exact resolve eq44 eq378112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379200 : ∀ X0 X1 X2 : G, x = y ∨ (M.op X1 (σ y)) = (M.op X1 (M.op (σ x) X2)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq379135 X0 X1 X2
       have j1 := eq237746 X1 X2
       grind)
    | (have r₁ := eq379135 X0 X1 X2
       have r₂ := eq237746 X0 X1
       grind)
    | exact resolve eq379135 eq237746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379135
  have eq775604 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq379140 X0 X1
       grind)
    | exact superpose eq379140 eq16
    | (have j1 := eq379140 X0 X1
       grind)
    | exact resolve eq16 eq379140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379140
  have eq775722 : ∀ X0 X1 : G, (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq775604 X0 X1
       grind)
    | (have r₁ := eq775604 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq775604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775604
  have eq775752 : ∀ X0 X1 : G, (M.op x y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq775722 X0 X1
       grind)
    | exact superpose eq775722 eq10
    | (have j1 := eq775722 X0 X1
       grind)
    | exact resolve eq10 eq775722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775722
  have eq776135 : ∀ X0 X1 : G, (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq775752 X0 X1
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq775752
    | (have j0 := eq775752 X0 X1
       grind)
    | exact resolve eq775752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775752
  have eq778534 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ x) = (σ y) ∨ (M.op X2 y) = (M.op X2 (M.op x X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X1 y X0 x
       have i₂ := eq776135 X2 X3
       grind)
    | exact superpose eq776135 eq44
    | (have j1 := eq776135 X2 X3
       grind)
    | exact resolve eq44 eq776135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776135
  have eq778637 : ∀ X0 X2 X3 : G, (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 (M.op x X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq778534 X0 x X2 X3
       have i₂ := eq44 x x X0 x
       grind)
    | exact superpose eq44 eq778534
    | (have j0 := eq778534 X0 x X2 X3
       grind)
    | exact resolve eq778534 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq778534
  have eq778649 : ∀ X0 X1 X2 : G, y = (τ (σ x)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 y
       have i₂ := eq778637 X0 X1 X2
       grind)
    | exact superpose eq778637 eq10
    | (have j1 := eq778637 X0 X1 X2
       grind)
    | exact resolve eq10 eq778637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778637
  have eq778999 : ∀ X0 X1 X2 : G, x = y ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq778649 X0 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq778649
    | (have j0 := eq778649 X0 X1 X2
       grind)
    | exact resolve eq778649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778649
  have eq781236 : ∀ X0 X1 X2 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16
       have i₂ := eq778999 X0 X1 X2
       grind)
    | exact superpose eq778999 eq16
    | (have j1 := eq778999 X0 X1 X2
       grind)
    | exact resolve eq16 eq778999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778999
  have eq781354 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq781236 X0 X1 X2
       grind)
    | (have r₁ := eq781236 X0 X1 X2
       have r₂ := eq22 x
       grind)
    | exact resolve eq781236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781236
  have eq852573 : ∀ X0 X1 X2 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (σ x) = (σ y) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16
       have i₂ := eq379200 X0 X1 X2
       grind)
    | exact superpose eq379200 eq16
    | (have j1 := eq379200 X2 X0 X1
       grind)
    | exact resolve eq16 eq379200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379200
  have eq852707 : ∀ X0 X1 X2 : G, (σ x) = (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq852573 X0 X1 X2
       grind)
    | (have r₁ := eq852573 X0 X1 X2
       have r₂ := eq22 x
       grind)
    | exact resolve eq852573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852573
  have eq852721 : ∀ X0 X1 X2 : G, y = (τ (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 y
       have i₂ := eq852707 X0 X1 X2
       grind)
    | exact superpose eq852707 eq10
    | (have j1 := eq852707 X0 X1 X2
       grind)
    | exact resolve eq10 eq852707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852707
  have eq853071 : ∀ X0 X1 X2 : G, x = y ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq852721 X0 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq852721
    | (have j0 := eq852721 X0 X1 X2
       grind)
    | exact resolve eq852721 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852721
  have eq855488 : ∀ X0 X1 X2 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16
       have i₂ := eq853071 X0 X1 X2
       grind)
    | exact superpose eq853071 eq16
    | (have j1 := eq853071 X0 X1 X2
       grind)
    | exact resolve eq16 eq853071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853071
  have eq855622 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X2 x) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq855488 X0 X1 X2
       grind)
    | (have r₁ := eq855488 X0 X1 X2
       have r₂ := eq22 x
       grind)
    | exact resolve eq855488 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855488
  have eq856173 : ∀ X0 X1 X2 X3 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 (σ y)) = (M.op X2 (M.op (σ x) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq237746 X0 X1
       have i₂ := eq855622 X2 X3 x
       grind)
    | exact superpose eq855622 eq237746
    | (have j0 := eq237746 X0 X1
       have j1 := eq855622 X0 X1 X2
       grind)
    | exact resolve eq237746 eq855622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237746 eq855622
  have eq856213 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (M.op X2 (σ y)) = (M.op X2 (M.op (σ x) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq856173 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856173
  have eq859598 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq856213 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856213
  have eq859599 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq859598 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859598
  have eq859608 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq859599 X1 (σ y)
       have i₂ := eq28895 X0
       grind)
    | exact superpose eq28895 eq859599
    | (have j1 := eq28895 X1
       grind)
    | exact resolve eq859599 eq28895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28895 eq859599
  have eq1005616 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq859608 X1 X0
       grind)
    | exact superpose eq859608 eq10
    | (have j1 := eq859608 X0 X0
       grind)
    | exact resolve eq10 eq859608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859608
  have eq1005972 : ∀ X0 X1 : G, x = y ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1005616 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1005616
    | (have j0 := eq1005616 X0 X0
       grind)
    | exact resolve eq1005616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005616
  have eq1008756 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1005972 X0 X1
       grind)
    | exact superpose eq1005972 eq16
    | (have j1 := eq1005972 X0 X0
       grind)
    | exact resolve eq16 eq1005972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005972
  have eq1008940 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq1008756 X0 X0
       grind)
    | (have r₁ := eq1008756 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq1008756 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008756
  have eq1009644 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1008940 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008940
  have eq1009645 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1009644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009644
  have eq1012957 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1009645 (σ x)
       grind)
    | exact superpose eq1009645 eq16
    | exact resolve eq16 eq1009645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009645
  have eq1013181 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1012957
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq1012957
    | exact resolve eq1012957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1012957
  have eq1014066 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1013181
       have i₂ := eq781354 x X0 X1
       grind)
    | exact superpose eq781354 eq1013181
    | (have j1 := eq781354 X0 X0 X1
       grind)
    | exact resolve eq1013181 eq781354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781354
  have eq1014071 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1014066 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014066
  have eq1016696 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1014071 X0 y
       have i₂ := eq378112
       grind)
    | exact superpose eq378112 eq1014071
    | exact resolve eq1014071 eq378112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378112 eq1014071
  have eq1017903 : ∀ X0 : G, x = y ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1016696 X0
       grind)
    | (have r₁ := eq1016696 X0
       have r₂ := eq1013181
       grind)
    | exact resolve eq1016696 eq1013181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016696
  have eq1044120 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1013181
       have i₂ := eq1017903 X0
       grind)
    | exact superpose eq1017903 eq1013181
    | (have j1 := eq1017903 X0
       grind)
    | exact resolve eq1013181 eq1017903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017903
  have eq1044125 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1044120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044120
  have eq1044194 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq1044125 X0
       grind)
    | exact superpose eq1044125 eq10
    | (have j1 := eq1044125 X0
       grind)
    | exact resolve eq10 eq1044125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044125
  have eq1044552 : ∀ X0 : G, x = y ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1044194 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1044194
    | (have j0 := eq1044194 X0
       grind)
    | exact resolve eq1044194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044194
  have eq1046973 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1013181
       have i₂ := eq1044552 X0
       grind)
    | exact superpose eq1044552 eq1013181
    | (have j1 := eq1044552 X0
       grind)
    | exact resolve eq1013181 eq1044552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044552
  have eq1046978 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1046973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046973
  have eq1047584 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1013181
       have i₂ := eq1046978 x
       grind)
    | exact superpose eq1046978 eq1013181
    | exact resolve eq1013181 eq1046978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013181 eq1046978
  have eq1047601 : False := by grind
  exact eq1047601

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pxy_y_Equation3583 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law3583 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq15 X0 X1
       have r₂ := eq12 (σ (k X0 X1)) (k (σ X0) (σ X1))
       grind)
    | (have r₁ := eq15 X0 X1
       have r₂ := eq12 (k (σ X0) (σ X1)) (σ (k X0 X1))
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19
    | exact resolve eq19 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq47 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq48 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq48 eq9
    | exact resolve eq9 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X2
       have i₂ := eq48 X0 X1 X2
       grind)
    | exact superpose eq48 eq13
    | (have j0 := eq13 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq13 (M.op X0 X1) x
       have r₂ := eq48 X0 X1 x
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq60 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq10
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq26 (σ X0) (σ X0)
       grind)
    | exact superpose eq26 eq67
    | exact resolve eq67 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq59
    | exact resolve eq59 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq73 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 X0 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq26
    | exact resolve eq26 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq70 (τ X0)
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq336 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) (σ X2)) = (σ (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X0 X1) X2
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq15
    | (have j1 := eq62 X0 X1 X2
       grind)
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq843 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X0)) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X0 X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq336
    | (have j0 := eq336 X0 X0 X1
       grind)
    | exact resolve eq336 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq336
  have eq906 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq928 : (M.op (σ x) (σ y)) ≠ (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq906 x y
       grind)
    | exact superpose eq906 eq16
    | (have j1 := eq906 x y
       grind)
    | exact resolve eq16 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (k (M.op (σ X0) (σ X0)) (σ X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X1)
       have i₂ := eq906 X0 X1
       grind)
    | exact superpose eq906 eq10
    | (have j1 := eq906 X0 X1
       grind)
    | exact resolve eq10 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq976 : ∀ X0 X1 : G, (M.op X0 X1) = (k (τ (M.op (σ X0) (σ X0))) (τ (σ X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq937 X0 X1
       have i₂ := eq26 (σ X1) (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq26 eq937
    | (have j0 := eq937 X0 X1
       grind)
    | exact resolve eq937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq937
  have eq986 : ∀ X0 X1 : G, (M.op X0 X1) = (k (τ (M.op (σ X0) (σ X0))) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq976 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq976
    | (have j0 := eq976 X0 X1
       grind)
    | exact resolve eq976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq991 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (τ (σ X0)) (τ (σ X0))) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq986 X0 X1
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq986
    | (have j0 := eq986 X0 X1
       grind)
    | exact resolve eq986 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq986
  have eq995 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq991 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq991
    | (have j0 := eq991 X0 X1
       grind)
    | exact resolve eq991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1578 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq928
       have i₂ := eq995 (σ x) (σ y)
       grind)
    | exact superpose eq995 eq928
    | (have j1 := eq995 x y
       grind)
    | (have r₁ := eq928
       have r₂ := eq995 (σ x) (σ y)
       grind)
    | exact resolve eq928 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1584 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1578
  have eq1589 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72 x
       have i₂ := eq1584
       grind)
    | exact superpose eq1584 eq72
    | exact resolve eq72 eq1584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1584
  have eq1618 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1589
  have eq1619 : (M.op (σ x) (M.op (σ x) (σ x))) ≠ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq928
       have i₂ := eq1618
       grind)
    | exact superpose eq1618 eq928
    | exact resolve eq928 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1620 : (σ (M.op x y)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1618
       grind)
    | exact superpose eq1618 eq16
    | exact resolve eq16 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1667 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1620
       have i₂ := eq48 (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq48 eq1620
    | exact resolve eq1620 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1668 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ≠ (M.op (σ x) (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1619
       have i₂ := eq70 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq70 eq1619
    | exact resolve eq1619 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1619
  have eq1671 : (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1668
       have i₂ := eq48 (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq48 eq1668
    | exact resolve eq1668 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1672 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1671
       have i₂ := eq48 (σ x) (σ x) (M.op (σ x) (σ x))
       grind)
    | exact superpose eq48 eq1671
    | (have r₁ := eq1671
       have r₂ := eq48 (σ x) (σ x) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq1671 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq1673 : y = (M.op x x) := by grind
  clear eq1672
  have eq1682 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq48 x x x
       have i₂ := eq1673
       grind)
    | exact superpose eq1673 eq48
    | exact resolve eq48 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1673
  have eq1766 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1667
       have i₂ := eq1682 x
       grind)
    | exact superpose eq1682 eq1667
    | exact resolve eq1667 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667 eq1682
  have eq1767 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1766
       have i₂ := eq1618
       grind)
    | exact superpose eq1618 eq1766
    | (have r₁ := eq1766
       have r₂ := eq1618
       grind)
    | exact resolve eq1766 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq1766
  have eq1768 : False := by grind
  exact eq1768

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxy_x_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq50 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op (M.op (M.op X1 X0) X1) X2) = (k (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) X1) X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq44
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq44 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq128 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq22
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq139 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq215 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y X0
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 X0) X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq233 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq215 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) X0
       have r₂ := eq215 X0
       grind)
    | exact resolve eq13 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq260 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq313 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq236 eq130
    | exact resolve eq130 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq314 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq215 eq313
    | exact resolve eq313 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq313
  have eq317 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq314
    | exact resolve eq314 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq320 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq317 eq94
    | (have j0 := eq94 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq321 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq320
  have eq325 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq321 eq54
    | exact resolve eq54 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq331 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq325 eq13
    | (have j0 := eq13 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) X0
       have r₂ := eq325 X0
       grind)
    | exact resolve eq13 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq566 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X1) X2) = (k (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | (have r₁ := eq66 X0 X1 X2
       have r₂ := eq221 X0 X1
       grind)
    | exact resolve eq66 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq566 X0 X1 X2
       have i₂ := eq221 X0 X1
       grind)
    | exact superpose eq221 eq566
    | exact resolve eq566 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq755 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq260 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq260
    | (have j0 := eq260 X0 y
       grind)
    | exact resolve eq260 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq830 : (k (k (M.op x y) x) y) = (τ (k (k (σ (M.op x y)) (σ x)) (σ y))) := by
    first
    | exact superpose eq139 eq755
    | exact resolve eq755 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq755
  have eq848 : (k (k (M.op x y) x) y) = (τ (k (M.op (σ (M.op x y)) (σ x)) (σ y))) := by
    first
    | exact superpose eq334 eq830
    | exact resolve eq830 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq830
  have eq854 : (k (k (M.op x y) x) y) = (τ (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) := by
    first
    | (have i₁ := eq848
       have i₂ := eq567 sF1 sF2 sF3
       grind)
    | exact superpose eq567 eq848
    | exact resolve eq848 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq859 : (τ (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) = (k (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq236 eq854
    | exact resolve eq854 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq854
  have eq863 : (τ (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq567 sF0 x y
       grind)
    | exact superpose eq567 eq859
    | exact resolve eq859 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq859
  have eq866 : (τ (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) = (M.op (M.op y x) y) := by
    first
    | exact superpose eq222 eq863
    | exact resolve eq863 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq863
  have eq867 : (M.op x y) = (τ (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) := by
    first
    | (have i₁ := eq866
       have i₂ := eq221 x y
       grind)
    | exact superpose eq221 eq866
    | exact resolve eq866 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq866
  have eq868 : (M.op x y) = (τ (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) := by
    first
    | (have i₁ := eq867
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq867
    | exact resolve eq867 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq869 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq868 eq15
    | exact resolve eq15 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq881 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq20 eq869
    | exact resolve eq869 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq120
  have eq1088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1087
    | exact resolve eq1087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1091 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1088
       have r₂ := eq27
       grind)
    | exact resolve eq1088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1096 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1091 eq54
    | exact resolve eq54 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1167 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq881 eq1096
    | exact resolve eq1096 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq1096
  have eq1190 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq54 y x x
       have i₂ := eq1167
       grind)
    | exact superpose eq1167 eq54
    | exact resolve eq54 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1167
  have eq1235 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1190 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1190
    | (have j0 := eq1190 x
       grind)
    | exact resolve eq1190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1190
  have eq1249 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1235 eq29
    | exact resolve eq29 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1235
  have eq1272 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1249
    | exact resolve eq1249 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1249
  have eq1273 : y = (M.op x y) := by grind
  clear eq1272
  have eq1288 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1273 eq20
    | exact resolve eq20 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1273
  have eq1310 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1288
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1288
    | exact resolve eq1288 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1288
  have eq1314 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1310 eq26
    | exact resolve eq26 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1310
  have eq1339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq325 eq1314
    | exact resolve eq1314 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq1314
  have eq1346 : False := by grind
  exact eq1346

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_pxx_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq51 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq60 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq86 : (σ (k y (k x x))) = (k (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq37 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq37
    | exact resolve eq37 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq89 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq94 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq101 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op X1 X0) X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X1 X0) X1) = (M.op (M.op (M.op X1 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq110 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq227 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62
    | (have j0 := eq62 x y X0
       grind)
    | exact resolve eq62 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq62
    | (have j0 := eq62 (σ x) (σ y) X0
       grind)
    | exact resolve eq62 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X1 X0) X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq227 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq227 (M.op x y)
       grind)
    | exact resolve eq13 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq277 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq228 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq228 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq319 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq248 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq322 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq319 eq130
    | exact resolve eq130 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq319
  have eq326 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq322
    | exact resolve eq322 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq329 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq326 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq330 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq329
  have eq334 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq330 eq62
    | exact resolve eq62 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq277 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq480 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq69
    | (have j0 := eq69 X0 (M.op x y)
       grind)
    | exact resolve eq69 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq490 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq489 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq498 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq334 eq480
    | (have j0 := eq480 X0
       grind)
    | exact resolve eq480 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq504 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq334 eq498
    | (have j0 := eq498 X0
       grind)
    | exact resolve eq498 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq498
  have eq547 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X1 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X1 X0)
       have i₂ := eq229 X0 X1
       grind)
    | exact superpose eq229 eq13
    | (have j0 := eq13 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq229 X0 X0
       grind)
    | exact resolve eq13 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X1 X0) X1)) ∨ (M.op (M.op X1 X0) X1) = (M.op (M.op (M.op X1 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq62 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq62 eq101
    | (have j0 := eq101 X0 X1
       grind)
    | exact resolve eq101 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq609 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X1 X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq608 X0 X1
       have j1 := eq13 (M.op X0 X1) (M.op (M.op X1 X0) X1)
       grind)
    | (have r₁ := eq608 X0 X1
       have r₂ := eq13 (M.op X0 X1) (M.op (M.op X1 X0) X1)
       grind)
    | exact resolve eq608 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq610 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq229 X0 X1
       grind)
    | exact superpose eq229 eq609
    | exact resolve eq609 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq713 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq310 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq310
    | (have j0 := eq310 y X0
       grind)
    | exact resolve eq310 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq766 : (k y (k x x)) = (τ (k (σ y) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq50 eq713
    | exact resolve eq713 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq4356 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq490 (M.op X0 X1)
       have i₂ := eq610 X0 X1
       grind)
    | exact superpose eq610 eq490
    | (have j0 := eq490 (M.op X0 X1)
       grind)
    | exact resolve eq490 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq610
  have eq4370 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356
  have eq4528 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq504 eq91
    | (have j1 := eq504 y
       grind)
    | exact resolve eq91 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq4561 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4528
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4528
    | exact resolve eq4528 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528
  have eq4591 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4561
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4561
    | exact resolve eq4561 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq12571 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4591 eq117
    | exact resolve eq117 eq4591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq4591
  have eq12591 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq31 eq12571
    | exact resolve eq12571 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12571
  have eq14839 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq547 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq18850 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq4370 X0 X1
       grind)
    | exact superpose eq4370 eq62
    | exact resolve eq62 eq4370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4370
  have eq20289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq20296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq20289
    | exact resolve eq20289 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20289
  have eq20307 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq20296
       have r₂ := eq28
       grind)
    | exact resolve eq20296 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20296
  have eq20315 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20307 eq62
    | exact resolve eq62 eq20307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20307
  have eq20340 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq20315
    | (have j0 := eq20315 (σ x)
       grind)
    | exact resolve eq20315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20315
  have eq20661 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20340 eq229
    | exact resolve eq229 eq20340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20340
  have eq20674 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20661
    | exact resolve eq20661 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20661
  have eq20691 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18850 y x x
       have i₂ := eq20674
       grind)
    | exact superpose eq20674 eq18850
    | exact resolve eq18850 eq20674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20674
  have eq20695 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20691 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20691
    | (have j0 := eq20691 X0
       grind)
    | exact resolve eq20691 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20691
  have eq52854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20695 eq27
    | (have j1 := eq20695 (σ x)
       grind)
    | exact resolve eq27 eq20695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20695
  have eq52857 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq52854
  have eq53208 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq229 y y
       have i₂ := eq52857
       grind)
    | exact superpose eq52857 eq229
    | exact resolve eq229 eq52857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq52857
  have eq53228 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53208
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53208
    | exact resolve eq53208 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53208
  have eq53233 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53228 eq28
    | exact resolve eq28 eq53228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53236 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53228 eq228
    | exact resolve eq228 eq53228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq53238 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53228 eq395
    | exact resolve eq395 eq53228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53228
  have eq55375 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53236 eq12591
    | exact resolve eq12591 eq53236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53236
  have eq55378 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55375
  have eq55394 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq55378
       have r₂ := eq53233
       grind)
    | exact resolve eq55378 eq53233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55378
  have eq55401 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53238 eq110
    | exact resolve eq110 eq53238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq53238
  have eq55446 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq55401
    | exact resolve eq55401 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55401
  have eq56972 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55394 eq91
    | exact resolve eq91 eq55394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55394
  have eq57000 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq56972
    | exact resolve eq56972 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56972
  have eq57029 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq55446
       grind)
    | exact superpose eq55446 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq55446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55446
  have eq57036 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57029
  have eq57180 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 y y x
       have i₂ := eq57036
       grind)
    | exact superpose eq57036 eq62
    | exact resolve eq62 eq57036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57036
  have eq57228 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y X1
       have i₂ := eq57180 (M.op y X0)
       grind)
    | exact superpose eq57180 eq14
    | exact resolve eq14 eq57180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57180
  have eq64301 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57228 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57228
    | (have j0 := eq57228 x X0
       grind)
    | exact resolve eq57228 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57228
  have eq64488 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14839 y
       have i₂ := eq64301 y
       grind)
    | exact superpose eq64301 eq14839
    | exact resolve eq14839 eq64301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14839 eq64301
  have eq64567 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64488 eq91
    | exact resolve eq91 eq64488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq64488
  have eq64619 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64567
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64567
    | exact resolve eq64567 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64567
  have eq64727 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64619 eq57000
    | exact resolve eq57000 eq64619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57000 eq64619
  have eq64742 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64727
  have eq64758 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq64742
       have r₂ := eq53233
       grind)
    | exact resolve eq64742 eq53233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53233 eq64742
  have eq64784 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64758 eq52
    | (have r₁ := eq52
       have r₂ := eq64758
       grind)
    | exact resolve eq52 eq64758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq64789 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64758 eq395
    | exact resolve eq395 eq64758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq64800 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq64784
  have eq64898 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64789 eq50
    | exact resolve eq50 eq64789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64789
  have eq64947 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq64898
    | exact resolve eq64898 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64898
  have eq64953 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64800 eq99
    | exact resolve eq99 eq64800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64800
  have eq64980 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq64953
    | exact resolve eq64953 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64953
  have eq64984 : y = (k y x) := by
    first
    | (have r₁ := eq64980
       have r₂ := eq51
       grind)
    | exact resolve eq64980 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq64980
  have eq64986 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq64984
       grind)
    | exact superpose eq64984 eq89
    | exact resolve eq89 eq64984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65025 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq64986
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64986
    | exact resolve eq64986 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64986
  have eq65187 : (k (σ y) (k (σ x) (σ x))) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq64947
       grind)
    | exact superpose eq64947 eq86
    | exact resolve eq86 eq64947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq65208 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq64947
       grind)
    | exact superpose eq64947 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq64947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64947
  have eq65215 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq65208
  have eq65240 : (k (σ y) (σ x)) = (k (σ y) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65187
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq65187
    | exact resolve eq65187 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq65187
  have eq65248 : (σ y) = (k (σ y) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65025 eq65240
    | exact resolve eq65240 eq65025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65240
  have eq65319 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq62 x x x
       have i₂ := eq65215
       grind)
    | exact superpose eq65215 eq62
    | exact resolve eq62 eq65215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65215
  have eq65389 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq65319 y
       grind)
    | exact superpose eq65319 eq100
    | exact resolve eq100 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq65397 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq65389
  have eq65412 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq65025 eq65397
    | exact resolve eq65397 eq65025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65025 eq65397
  have eq65419 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65412
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65412
    | exact resolve eq65412 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65412
  have eq67068 : (τ (σ y)) = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65248 eq766
    | exact resolve eq766 eq65248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq65248
  have eq67082 : y = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq67068
    | exact resolve eq67068 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67068
  have eq71396 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65319 x
       have i₂ := eq65419
       grind)
    | exact superpose eq65419 eq65319
    | exact resolve eq65319 eq65419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65319
  have eq71415 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18850 x x x
       have i₂ := eq65419
       grind)
    | exact superpose eq65419 eq18850
    | exact resolve eq18850 eq65419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18850 eq65419
  have eq71422 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq71396
  have eq71441 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq71415 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq71415
    | (have j0 := eq71415 X0
       grind)
    | exact resolve eq71415 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71415
  have eq71450 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq71422 eq30
    | exact resolve eq30 eq71422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq71422
  have eq71709 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq71450
    | exact resolve eq71450 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq71450
  have eq71710 : x = (M.op x y) ∨ x = y := by grind
  clear eq71709
  have eq107656 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq71441
    | (have j0 := eq71441 (σ x)
       grind)
    | exact resolve eq71441 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71441
  have eq107753 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq107656 eq64758
    | exact resolve eq64758 eq107656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64758 eq107656
  have eq107756 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq107753
  have eq108555 : (τ (k (σ x) (σ x))) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107756 eq99
    | exact resolve eq99 eq107756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq107756
  have eq108839 : y = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108555
       have i₂ := eq64984
       grind)
    | exact superpose eq64984 eq108555
    | exact resolve eq108555 eq64984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108555
  have eq108854 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50 eq108839
    | exact resolve eq108839 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq108839
  have eq109703 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67082
       have i₂ := eq108854
       grind)
    | exact superpose eq108854 eq67082
    | exact resolve eq67082 eq108854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67082 eq108854
  have eq109737 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq109703
  have eq110723 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq109737
       grind)
    | exact superpose eq109737 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq109737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109737
  have eq110730 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq110723
  have eq112527 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq62 y y x
       have i₂ := eq110730
       grind)
    | exact superpose eq110730 eq62
    | exact resolve eq62 eq110730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq110730
  have eq114275 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112527 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112527
    | (have j0 := eq112527 x
       grind)
    | exact resolve eq112527 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq112527
  have eq114525 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq114275
  have eq114529 : x = (M.op x y) := by
    first
    | (have r₁ := eq114525
       have r₂ := eq71710
       grind)
    | exact resolve eq114525 eq71710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71710 eq114525
  have eq114666 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq114529 eq21
    | exact resolve eq21 eq114529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq114969 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114666
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq114666
    | exact resolve eq114666 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114666
  have eq114992 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq114969 eq27
    | exact resolve eq27 eq114969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq117534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq114992 eq12591
    | exact resolve eq12591 eq114992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12591
  have eq117560 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have r₁ := eq117534
       have r₂ := eq28
       grind)
    | exact resolve eq117534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117534
  have eq117564 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq114529 eq117560
    | exact resolve eq117560 eq114529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114529 eq117560
  have eq117566 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq117564
       have i₂ := eq64984
       grind)
    | exact superpose eq64984 eq117564
    | exact resolve eq117564 eq64984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64984 eq117564
  have eq119795 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq117566 eq114992
    | exact resolve eq114992 eq117566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117566
  have eq119823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq330 eq119795
    | exact resolve eq119795 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119795
  have eq119937 : x = y := by
    first
    | (have r₁ := eq119823
       have r₂ := eq28
       grind)
    | exact resolve eq119823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119823
  have eq120176 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq119937
       grind)
    | exact superpose eq119937 eq25
    | exact resolve eq25 eq119937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq119937
  have eq120529 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq120176
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq120176
    | exact resolve eq120176 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq120176
  have eq120658 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq114969 eq120529
    | exact resolve eq120529 eq114969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114969 eq120529
  have eq126122 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq120658 eq114992
    | exact resolve eq114992 eq120658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114992 eq120658
  have eq126126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq330 eq126122
    | exact resolve eq126122 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq126122
  have eq126239 : False := by grind
  exact eq126239

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pyy_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X1) X2) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X1) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X1 X0) X1) = (k (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) X1) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) X1) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) X1) (M.op X0 X1)
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq64 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq64 X0 X1 X2
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq68 X1 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) ∨ (M.op (σ X0) X1) ≠ (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq80 X1 (σ X0)
       grind)
    | exact superpose eq80 eq28
    | (have j1 := eq80 (σ X0) X1
       grind)
    | exact resolve eq28 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (M.op (τ X0) X1) ≠ (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) X1)
       have i₂ := eq80 X1 (τ X0)
       grind)
    | exact superpose eq80 eq17
    | (have j1 := eq80 (τ X0) X1
       grind)
    | exact resolve eq17 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (M.op X1 (τ X0)) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (σ X0) X1) ≠ (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq428 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq428 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq450 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X1 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X2 X0
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
  have eq460 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq462 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq457 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq478 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X0 x
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq64
    | (have j1 := eq461 X0
       grind)
    | exact resolve eq64 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 X0 X0
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq89
    | (have j1 := eq461 X0
       grind)
    | exact resolve eq89 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq478 (σ X0) X1
       grind)
    | exact superpose eq478 eq15
    | (have j1 := eq478 (σ X0) X1
       grind)
    | exact resolve eq15 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq535 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq482 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq482
    | exact resolve eq482 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq482 (τ X0)
       grind)
    | exact superpose eq482 eq17
    | (have j1 := eq482 (τ X0)
       grind)
    | exact resolve eq17 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq553
    | (have j0 := eq553 X0
       grind)
    | exact resolve eq553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq575 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq559 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq559
    | (have j0 := eq559 X0
       grind)
    | exact resolve eq559 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq642 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X2)) = (M.op X0 X2) ∨ (M.op X0 X4) = X0 ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X1 X0 X2 X3
       have i₂ := eq450 X0 (M.op X0 X1) X4
       grind)
    | exact superpose eq450 eq61
    | (have j1 := eq450 X0 X1 X4
       grind)
    | exact resolve eq61 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = X0 ∨ (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq450 X0 (M.op X0 X1) X3
       grind)
    | exact superpose eq450 eq9
    | (have j1 := eq450 X0 X1 X3
       grind)
    | exact resolve eq9 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq652 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X0) X2) = (M.op X0 X2) ∨ (M.op X0 X4) = X0 ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq642 X0 X1 X2 x X4
       have i₂ := eq64 (M.op X1 X0) X2 x
       grind)
    | exact superpose eq64 eq642
    | (have j0 := eq642 X0 X1 X2 x X4
       grind)
    | exact resolve eq642 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq696 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq63 X1 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq63 X1 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq726 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X0)
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq68
    | (have j1 := eq509 X0 X1
       grind)
    | exact resolve eq68 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq509 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq750 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq734 (M.op X0 X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq734
    | (have j0 := eq734 (M.op X0 X1)
       grind)
    | exact resolve eq734 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq734 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq734
    | (have j0 := eq734 (τ X0)
       grind)
    | exact resolve eq734 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq750 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq756 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq754 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq754
    | (have j0 := eq754 X0
       grind)
    | exact resolve eq754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq759 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq756 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq756
    | (have j0 := eq756 X0
       grind)
    | exact resolve eq756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq769 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq759 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq759
    | (have j0 := eq759 (τ X0)
       grind)
    | exact resolve eq759 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq772 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq755 X0 X0
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq755
    | (have j1 := eq461 (σ X0)
       grind)
    | exact resolve eq755 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq788 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq755 X0 X1
       grind)
    | exact superpose eq755 eq64
    | exact resolve eq64 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ X2 ∨ (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (σ (M.op X0 X1)) (σ (M.op X0 X1)) X2
       have i₂ := eq755 X0 X1
       grind)
    | exact superpose eq755 eq70
    | (have r₁ := eq70 (σ (M.op X0 X1)) (σ (M.op X0 X1)) (σ (M.op X0 X1))
       have r₂ := eq755 X0 X1
       grind)
    | exact resolve eq70 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq936 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq769 (M.op X0 X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq769
    | (have j0 := eq769 (M.op X0 X1)
       grind)
    | exact resolve eq769 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq936 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq980 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq945 X0 X1
       grind)
    | exact superpose eq945 eq64
    | exact resolve eq64 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1178 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ X0)) X1) = (M.op X2 (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X2 x
       have i₂ := eq772 X0
       grind)
    | exact superpose eq772 eq61
    | (have j1 := eq772 X0
       grind)
    | exact resolve eq61 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1184 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq89 (σ X0) (σ X0)
       have i₂ := eq772 X0
       grind)
    | exact superpose eq772 eq89
    | (have j1 := eq772 X0
       grind)
    | exact resolve eq89 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq772
  have eq1197 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1184 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1184
    | (have j0 := eq1184 X0
       grind)
    | exact resolve eq1184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1199 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (σ X0) X1) = (M.op (M.op (σ X0) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1178 X0 X1 x
       have i₂ := eq64 (σ X0) X1 x
       grind)
    | exact superpose eq64 eq1178
    | (have j0 := eq1178 X0 X1 x
       grind)
    | exact resolve eq1178 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1209 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq1197 (τ X0)
       grind)
    | exact superpose eq1197 eq18
    | (have j1 := eq1197 (τ X0)
       grind)
    | exact resolve eq18 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1248 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1209 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1209
    | (have j0 := eq1209 X0
       grind)
    | exact resolve eq1209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1253 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1248 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1248
    | (have j0 := eq1248 X0
       grind)
    | exact resolve eq1248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1861 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (k X0 X0))) ∨ (τ (k X0 X0)) ≠ (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq80 (τ X0) (τ X0)
       have i₂ := eq1253 X0
       grind)
    | exact superpose eq1253 eq80
    | (have j1 := eq1253 X0
       grind)
    | exact resolve eq80 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1253
  have eq1871 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1877 : ∀ X0 : G, (τ X0) = (τ (k X0 (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1871 X0
       have i₂ := eq31 (k X0 X0) X0
       grind)
    | exact superpose eq31 eq1871
    | (have j0 := eq1871 X0
       grind)
    | exact resolve eq1871 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1951 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (k X0 X0))
       have i₂ := eq1877 X0
       grind)
    | exact superpose eq1877 eq11
    | (have j1 := eq1877 X0
       grind)
    | exact resolve eq11 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq1964 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1951 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1951
    | (have j0 := eq1951 X0
       grind)
    | exact resolve eq1951 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2002 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1964 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1964
    | exact resolve eq1964 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X0))
       have i₂ := eq1964 (τ X0)
       grind)
    | exact superpose eq1964 eq17
    | (have j1 := eq1964 (τ X0)
       grind)
    | exact resolve eq17 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq2020 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2015 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2015
    | (have j0 := eq2015 X0
       grind)
    | exact resolve eq2015 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq2033 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2002 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq2002
    | (have j0 := eq2002 X0
       grind)
    | exact resolve eq2002 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2036 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2020 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2020
    | (have j0 := eq2020 X0
       grind)
    | exact resolve eq2020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2048 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2036 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq2036
    | (have j0 := eq2036 X0
       grind)
    | exact resolve eq2036 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2146 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (k X0 X0) X1
       have i₂ := eq2048 X0
       grind)
    | exact superpose eq2048 eq18
    | (have j1 := eq2048 X0
       grind)
    | exact resolve eq18 eq2048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2156 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k (σ X1) X0) = (k (σ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2146 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2146
    | (have j0 := eq2146 X0 X1
       grind)
    | exact resolve eq2146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2281 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = X0 ∨ (k (M.op X1 X2) X0) = X0 ∨ (M.op X1 X2) = X0 ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X1 X2 X0
       have i₂ := eq462 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq462 eq64
    | (have j1 := eq462 X0 X3 X3
       grind)
    | exact resolve eq64 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2299 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq2300 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2299 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299
  have eq4461 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2300 X0 X1
       grind)
    | exact superpose eq2300 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2300 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq2300 X0 X1
       grind)
    | exact resolve eq12 eq2300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4466 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq2300 X0 X1
       grind)
    | exact superpose eq2300 eq68
    | (have j1 := eq2300 X0 X1
       grind)
    | exact resolve eq68 eq2300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300
  have eq4510 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4461 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461
  have eq5235 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4510 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510
  have eq5306 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5235 X2 (M.op X0 X1)
       have i₂ := eq64 X0 X1 X2
       grind)
    | exact superpose eq64 eq5235
    | (have j0 := eq5235 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq5235 x (M.op X0 X1)
       have r₂ := eq64 X0 X1 x
       grind)
    | exact resolve eq5235 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5235
  have eq5357 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5306 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306
  have eq5531 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5357 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357
  have eq5567 : ∀ X0 X1 X3 : G, (σ (M.op X0 X1)) ≠ X3 ∨ (k X3 (σ (M.op X0 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq5531 X0 x (σ (M.op X0 X1))
       have i₂ := eq788 X0 X1 x
       grind)
    | exact superpose eq788 eq5531
    | (have r₁ := eq5531 (σ (M.op X0 X1)) x (σ (M.op X0 X1))
       have r₂ := eq788 X0 X1 x
       grind)
    | exact resolve eq5531 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5531
  have eq6323 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq11
    | (have j1 := eq575 X0
       grind)
    | exact resolve eq11 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6341 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6323 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6323
    | (have j0 := eq6323 X0
       grind)
    | exact resolve eq6323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6323
  have eq6443 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6341 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6341
    | (have j0 := eq6341 (σ X0)
       grind)
    | exact resolve eq6341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6503 : ∀ X0 X1 : G, (k (M.op (τ X0) (τ X0)) (τ X1)) = (τ (k (k X0 X0) X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq6341 X0
       grind)
    | exact superpose eq6341 eq28
    | (have j1 := eq6341 X0
       grind)
    | exact resolve eq28 eq6341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6341
  have eq6529 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6443 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6443
    | (have j0 := eq6443 X0
       grind)
    | exact resolve eq6443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6443
  have eq6539 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6529 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6529
    | (have j0 := eq6529 X0
       grind)
    | exact resolve eq6529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6529
  have eq6547 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq535 X0
       have i₂ := eq6539 X0
       grind)
    | exact superpose eq6539 eq535
    | (have j0 := eq535 X0
       have j1 := eq6539 X0
       grind)
    | exact resolve eq535 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq6578 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539
  have eq6597 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6547 X0
       have j1 := eq6578 X0
       grind)
    | (have r₁ := eq6547 X0
       have r₂ := eq6578 X0
       grind)
    | exact resolve eq6547 eq6578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6547 eq6578
  have eq7883 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq6597 (τ X0)
       grind)
    | exact superpose eq6597 eq18
    | (have j1 := eq6597 (τ X0)
       grind)
    | exact resolve eq18 eq6597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7884 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq734 X0
       have i₂ := eq6597 X0
       grind)
    | exact superpose eq6597 eq734
    | (have j0 := eq734 X0
       have j1 := eq6597 X0
       grind)
    | (have r₁ := eq734 X0
       have r₂ := eq6597 X0
       grind)
    | exact resolve eq734 eq6597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq6597
  have eq7915 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7884
  have eq7934 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7883 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7883
    | (have j0 := eq7883 X0
       grind)
    | exact resolve eq7883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7883
  have eq7939 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7934 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7934
    | (have j0 := eq7934 X0
       grind)
    | exact resolve eq7934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7934
  have eq8426 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq7939 X0
       grind)
    | exact superpose eq7939 eq10
    | (have j1 := eq7939 X0
       grind)
    | exact resolve eq10 eq7939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7939
  have eq8494 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq769 X0
       have i₂ := eq8426 X0
       grind)
    | exact superpose eq8426 eq769
    | (have j0 := eq769 X0
       have j1 := eq8426 X0
       grind)
    | exact resolve eq769 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq8534 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq8426 (σ X0)
       grind)
    | exact superpose eq8426 eq28
    | (have j1 := eq8426 (σ X0)
       grind)
    | exact resolve eq28 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8426
  have eq8539 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8494 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8494
  have eq8546 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8534 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8534
    | (have j0 := eq8534 X0
       grind)
    | exact resolve eq8534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8534
  have eq8563 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8546 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8546
    | (have j0 := eq8546 X0
       grind)
    | exact resolve eq8546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8546
  have eq8744 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq8563 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8563
    | (have j0 := eq8563 (τ X0)
       grind)
    | exact resolve eq8563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8563
  have eq8821 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8744 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq8744
    | (have j0 := eq8744 X0
       grind)
    | exact resolve eq8744 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8744
  have eq13545 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq98 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq13646 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (σ (M.op (τ X0) (τ X0)))) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13545 (k X0 X0)
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq13545
    | (have j1 := eq575 X0
       grind)
    | exact resolve eq13545 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13545
  have eq13760 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have j0 := eq13646 X0
       have j1 := eq5567 (τ X0) (τ X0) (k X0 X0)
       grind)
    | (have r₁ := eq13646 X0
       have r₂ := eq5567 (τ X0) (τ X0) (k X0 X0)
       grind)
    | exact resolve eq13646 eq5567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567 eq13646
  have eq14880 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (k X0 (τ (σ X0))) (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq41 X0 (σ X0) (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq13760 (σ X0)
       grind)
    | exact superpose eq13760 eq41
    | exact resolve eq41 eq13760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13760
  have eq14891 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (k X0 (τ (σ X0))) (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14880 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq14880
    | exact resolve eq14880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14880
  have eq14931 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (k X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14891 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14891
    | exact resolve eq14891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14891
  have eq14953 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14931 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq14931
    | exact resolve eq14931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931
  have eq14961 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14953 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14953
    | exact resolve eq14953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14953
  have eq25017 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq30873 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7915 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915
  have eq31233 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = X0 ∨ (k (M.op X3 X4) X0) = X0 ∨ (M.op X3 X4) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq64 X0 X3 X3
       have i₂ := eq2281 X0 X1 X2 X3
       grind)
    | exact superpose eq2281 eq64
    | (have j1 := eq2281 X0 X3 X4 X1
       grind)
    | exact resolve eq64 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31375 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2281 X0 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq31376 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31375
  have eq50111 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8539
  have eq59909 : ∀ X0 : G, (σ X0) ≠ (k (σ X0) (σ X0)) ∨ (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2156 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq59911 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq59909 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq59909
    | (have j0 := eq59909 X0
       grind)
    | exact resolve eq59909 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59909
  have eq59931 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 (k (τ (σ X0)) X0))) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59911 X0
       have i₂ := eq20 (σ X0) X0 X0
       grind)
    | exact superpose eq20 eq59911
    | (have j0 := eq59911 X0
       grind)
    | exact resolve eq59911 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq59911
  have eq59949 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59931 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59931
    | (have j0 := eq59931 X0
       grind)
    | exact resolve eq59931 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59931
  have eq59967 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq59949 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq59949
    | (have j0 := eq59949 X0
       grind)
    | exact resolve eq59949 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59949
  have eq69360 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = X0 ∨ (M.op X3 X0) = (M.op X4 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq64 X0 X3 X3
       have i₂ := eq644 X0 X1 X2 X3
       grind)
    | exact superpose eq644 eq64
    | (have j1 := eq644 X0 X3 X4 X1
       grind)
    | exact resolve eq64 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq72625 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq59967 X0
       have i₂ := eq2033 X0
       grind)
    | exact superpose eq2033 eq59967
    | (have j1 := eq2033 X0
       grind)
    | (have r₁ := eq59967 X0
       have r₂ := eq2033 X0
       grind)
    | exact resolve eq59967 eq2033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033 eq59967
  have eq72675 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq72625 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72625
  have eq72676 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq72675 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72675
  have eq72859 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq72676 X0
       grind)
    | exact superpose eq72676 eq10
    | exact resolve eq10 eq72676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72676
  have eq72951 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq72859 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72859
    | exact resolve eq72859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72859
  have eq79680 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4466 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq80159 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X1 X0) X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79680 (M.op X0 X1) X0
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq79680
    | (have j0 := eq79680 X0 X1
       grind)
    | exact resolve eq79680 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79680
  have eq86635 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq726 X0 (σ (k X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq92016 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X3 X1) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq69360 X1 X3 X2 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92038 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (k X3 X1) ∨ (M.op X0 X1) = (M.op X2 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq92016 X0 X1 X2 X3
       have j1 := eq69360 X1 X3 X2 X0 X2
       grind)
    | (have r₁ := eq92016 X0 X0 X2 X3
       have r₂ := eq69360 X0 X1 X2 X3 x
       grind)
    | exact resolve eq92016 eq69360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69360 eq92016
  have eq92637 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = (M.op X3 (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq92038 X2 (σ X1) X3 (σ X0)
       grind)
    | exact superpose eq92038 eq15
    | (have j1 := eq92038 X2 (σ X1) X3 X3
       grind)
    | exact resolve eq15 eq92038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92651 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq92038 X2 X1 X3 (τ X0)
       grind)
    | exact superpose eq92038 eq17
    | (have j1 := eq92038 X2 X1 X3 X3
       grind)
    | exact resolve eq17 eq92038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq92038
  have eq95494 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X1 (τ X0)) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30873 (τ X0)
       have i₂ := eq92651 X0 (τ X0) X2 x
       grind)
    | exact superpose eq92651 eq30873
    | (have j1 := eq92651 X0 (τ X0) X1 X2
       grind)
    | exact resolve eq30873 eq92651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30873 eq92651
  have eq95611 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ X0 ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X1 (τ X0)) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95494 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95494
    | (have j0 := eq95494 X0 X1 X2
       grind)
    | exact resolve eq95494 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95494
  have eq95699 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 ∨ (M.op X1 (τ X0)) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95611 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95611
    | (have j0 := eq95611 X0 X1 X2
       grind)
    | exact resolve eq95611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95611
  have eq95722 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 (τ X0)) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq95699 X0 X1 X2
       have j1 := eq482 X0
       grind)
    | (have r₁ := eq95699 X0 X1 X2
       have r₂ := eq482 X0
       grind)
    | exact resolve eq95699 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95699
  have eq95884 : ∀ X0 X1 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8821 X0
       have i₂ := eq95722 X0 X1 X2
       grind)
    | exact superpose eq95722 eq8821
    | (have j0 := eq8821 X0
       have j1 := eq95722 X0 X1 X2
       grind)
    | exact resolve eq8821 eq95722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8821 eq95722
  have eq96115 : ∀ X0 X1 X2 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = (M.op X2 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq95884 X0 X1 X2
       have j1 := eq50111 X0
       grind)
    | (have r₁ := eq95884 X0 X1 X2
       have r₂ := eq50111 X0
       grind)
    | exact resolve eq95884 eq50111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50111 eq95884
  have eq119941 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq92637 x y X0 X1
       grind)
    | exact superpose eq92637 eq16
    | (have j1 := eq92637 X0 y X0 X1
       grind)
    | exact resolve eq16 eq92637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92637
  have eq124632 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (M.op (σ (τ X0)) X1) = (M.op (M.op (σ (τ X0)) (σ (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq1199 (τ X0) X1
       grind)
    | exact superpose eq1199 eq31
    | (have j1 := eq1199 (τ X0) X1
       grind)
    | exact resolve eq31 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1199
  have eq124673 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq124632 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124632
    | (have j0 := eq124632 X0 X1
       grind)
    | exact resolve eq124632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124632
  have eq144809 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X0))) = (M.op X1 (σ (τ (k X0 X0)))) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq788 (τ X0) (τ X0) X2
       have i₂ := eq124673 X0 X1
       grind)
    | exact superpose eq124673 eq788
    | (have j1 := eq124673 X0 X2
       grind)
    | exact resolve eq788 eq124673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124673
  have eq144915 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144809 X0 X1 X2
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq144809
    | (have j0 := eq144809 X0 X1 X2
       grind)
    | exact resolve eq144809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144809
  have eq145428 : ∀ X0 : G, (k X0 X0) ≠ (M.op X0 (k X0 X0)) ∨ (M.op X0 (k X0 X0)) = (M.op (M.op X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq144915 X0 x (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145448 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (M.op X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq145428 X0
       have j1 := eq144915 X0 x (k X0 X0)
       grind)
    | (have r₁ := eq145428 x
       have r₂ := eq144915 x x x
       grind)
    | exact resolve eq145428 eq144915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144915 eq145428
  have eq145621 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k (k X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq430 X0 X0 (k X0 X0)
       have i₂ := eq145448 X0
       grind)
    | exact superpose eq145448 eq430
    | (have j0 := eq430 X0 X0 (k X0 X0)
       grind)
    | exact resolve eq430 eq145448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq145744 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq145621 X0
       have i₂ := eq14961 X0
       grind)
    | exact superpose eq14961 eq145621
    | (have j0 := eq145621 X0
       grind)
    | exact resolve eq145621 eq14961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14961 eq145621
  have eq249098 : ∀ X0 X1 : G, (M.op X1 (τ X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq96115 X0 X1 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96115
  have eq265837 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq249098 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq249098
    | exact resolve eq249098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249098
  have eq370455 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq25017 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25017
  have eq370465 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq370455 X0
       have j1 := eq652 X0 x x (M.op X0 X0)
       grind)
    | (have r₁ := eq370455 x
       have r₂ := eq652 x x x x
       grind)
    | (have r₁ := eq370455 x
       have r₂ := eq652 (M.op x x) x x x
       grind)
    | exact resolve eq370455 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq370455
  have eq370519 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq370465 X0
       have i₂ := eq64 X0 X0 X0
       grind)
    | exact superpose eq64 eq370465
    | (have j0 := eq370465 X0
       grind)
    | exact resolve eq370465 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370465
  have eq370534 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq370519 X0
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq370519
    | (have j0 := eq370519 X0
       grind)
    | exact resolve eq370519 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370519
  have eq370547 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq370534 X0
       have j1 := eq70 X0 X0 X0
       grind)
    | (have r₁ := eq370534 x
       have r₂ := eq70 x x (k (M.op x x) x)
       grind)
    | (have r₁ := eq370534 x
       have r₂ := eq70 x x x
       grind)
    | (have r₁ := eq370534 (M.op X0 x)
       have r₂ := eq70 X0 x (M.op (M.op X0 x) (M.op X0 x))
       grind)
    | exact resolve eq370534 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq370534
  have eq370813 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq370547 (τ X0)
       grind)
    | exact superpose eq370547 eq18
    | exact resolve eq18 eq370547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq372926 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq370813 (k X0 X0)
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq370813
    | (have j1 := eq575 X0
       grind)
    | exact resolve eq370813 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq370813
  have eq373479 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq372926 X0
       have j1 := eq790 (τ X0) (τ X0) (k X0 X0)
       grind)
    | (have r₁ := eq372926 X0
       have r₂ := eq790 (τ X0) (τ X0) (k (σ (M.op (τ X0) (τ X0))) (k X0 X0))
       grind)
    | (have r₁ := eq372926 X0
       have r₂ := eq790 (τ X0) (τ X0) (k X0 X0)
       grind)
    | exact resolve eq372926 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq372926
  have eq378066 : ∀ X0 : G, (τ (σ (M.op (τ X0) (τ X0)))) = (k (M.op (τ X0) (τ X0)) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op (τ X0) (τ X0)) (k X0 X0)
       have i₂ := eq373479 X0
       grind)
    | exact superpose eq373479 eq28
    | exact resolve eq28 eq373479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378082 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (σ X0) (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq373479 (σ X0)
       grind)
    | exact superpose eq373479 eq33
    | exact resolve eq33 eq373479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq373479
  have eq378116 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k (τ (σ (M.op X0 X0))) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq378082 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq378082
    | exact resolve eq378082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378082
  have eq378125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq378066 X0
       have i₂ := eq10 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq10 eq378066
    | exact resolve eq378066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378066
  have eq378326 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq378116 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq378116
    | exact resolve eq378116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378116
  have eq380289 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6503 X0 (k X0 X0)
       have i₂ := eq378125 X0
       grind)
    | exact superpose eq378125 eq6503
    | (have j0 := eq6503 X0 x
       grind)
    | exact resolve eq6503 eq378125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503 eq378125
  have eq436117 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (k X0 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0 (σ X0) (k (σ X0) (σ X0))
       have i₂ := eq380289 (σ X0)
       grind)
    | exact superpose eq380289 eq41
    | (have j1 := eq380289 (σ X0)
       grind)
    | exact resolve eq41 eq380289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq380289
  have eq436544 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (k X0 (τ (σ X0))) (k (τ (σ X0)) X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq436117 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq436117
    | (have j0 := eq436117 X0
       grind)
    | exact resolve eq436117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq436117
  have eq436622 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq436544 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq436544
    | (have j0 := eq436544 X0
       grind)
    | exact resolve eq436544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436544
  have eq436644 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq436622 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq436622
    | (have j0 := eq436622 X0
       grind)
    | exact resolve eq436622 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436622
  have eq436803 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq86635 X0
       have i₂ := eq436644 X0
       grind)
    | exact superpose eq436644 eq86635
    | (have j1 := eq436644 X0
       grind)
    | (have r₁ := eq86635 X0
       have r₂ := eq436644 X0
       grind)
    | exact resolve eq86635 eq436644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86635 eq436644
  have eq437028 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq436803 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436803
  have eq442594 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (τ (σ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265837 X0 X1
       have i₂ := eq437028 X0
       grind)
    | exact superpose eq437028 eq265837
    | (have j0 := eq265837 X0 X1
       have j1 := eq437028 X0
       grind)
    | exact resolve eq265837 eq437028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265837
  have eq442725 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (τ (σ X0))) ∨ (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq980 (σ X0) (σ X0) x
       have i₂ := eq437028 X0
       grind)
    | exact superpose eq437028 eq980
    | (have j1 := eq437028 X0
       grind)
    | exact resolve eq980 eq437028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980 eq437028
  have eq442864 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq442725 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq442725
    | (have j0 := eq442725 X0 X1
       grind)
    | exact resolve eq442725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442725
  have eq442926 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq442594 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq442594
    | (have j0 := eq442594 X0 X1
       grind)
    | exact resolve eq442594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442594
  have eq443025 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq442926 X0 X1
       have j1 := eq442864 X0 X1
       grind)
    | (have r₁ := eq442926 X0 X1
       have r₂ := eq442864 X0 X1
       grind)
    | exact resolve eq442926 eq442864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442926
  have eq443749 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X0 X0)) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq145744 (k X0 X0)
       have i₂ := eq442864 X0 X1
       grind)
    | exact superpose eq442864 eq145744
    | (have j1 := eq442864 X0 X1
       grind)
    | exact resolve eq145744 eq442864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442864
  have eq443933 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq443749 X0 X1
       have i₂ := eq64 X0 X0 (k X0 X0)
       grind)
    | exact superpose eq64 eq443749
    | (have j0 := eq443749 X0 X1
       grind)
    | exact resolve eq443749 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443749
  have eq443934 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq443933 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443933
  have eq444274 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (k X0 X0) (k X0 X0)
       have i₂ := eq443934 X0 X1
       grind)
    | exact superpose eq443934 eq68
    | (have j1 := eq443934 X0 X1
       grind)
    | exact resolve eq68 eq443934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443934
  have eq444406 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq444274 X0 X1
       have i₂ := eq145448 X0
       grind)
    | exact superpose eq145448 eq444274
    | (have j0 := eq444274 X0 X1
       grind)
    | exact resolve eq444274 eq145448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444274
  have eq444612 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (k X0 X0)
       have i₂ := eq444406 X0 X1
       grind)
    | exact superpose eq444406 eq68
    | (have j1 := eq444406 X0 X1
       grind)
    | exact resolve eq68 eq444406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444406
  have eq444757 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq444612 X0 X1
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq444612
    | (have j0 := eq444612 X0 X1
       grind)
    | exact resolve eq444612 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444612
  have eq445183 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq444757 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444757
  have eq449473 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X0 X0)) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq145744 (k X0 X0)
       have i₂ := eq443025 X0 X1
       grind)
    | exact superpose eq443025 eq145744
    | (have j1 := eq443025 X0 X1
       grind)
    | exact resolve eq145744 eq443025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443025
  have eq449663 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq449473 X0 X1
       have i₂ := eq64 X0 X0 (k X0 X0)
       grind)
    | exact superpose eq64 eq449473
    | (have j0 := eq449473 X0 X1
       grind)
    | exact resolve eq449473 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449473
  have eq449664 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq449663 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449663
  have eq450003 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (k X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (k X0 X0) (k X0 X0)
       have i₂ := eq449664 X0 X1
       grind)
    | exact superpose eq449664 eq68
    | (have j1 := eq449664 X0 X1
       grind)
    | exact resolve eq68 eq449664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449664
  have eq450136 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq450003 X0 X1
       have i₂ := eq145448 X0
       grind)
    | exact superpose eq145448 eq450003
    | (have j0 := eq450003 X0 X1
       grind)
    | exact resolve eq450003 eq145448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145448 eq450003
  have eq451002 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (k X0 X0)
       have i₂ := eq450136 X0 X1
       grind)
    | exact superpose eq450136 eq68
    | (have j1 := eq450136 X0 X1
       grind)
    | exact resolve eq68 eq450136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450136
  have eq451163 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq451002 X0 X1
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq451002
    | (have j0 := eq451002 X0 (k X0 X0)
       grind)
    | exact resolve eq451002 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451002
  have eq451610 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq451163 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451163
  have eq451611 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq451610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451610
  have eq451937 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31376 (k X0 X0) X0
       have i₂ := eq451611 X0
       grind)
    | exact superpose eq451611 eq31376
    | (have j0 := eq31376 X0 X0
       grind)
    | exact resolve eq31376 eq451611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31376
  have eq452070 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq451937 X0
       have i₂ := eq378326 X0
       grind)
    | exact superpose eq378326 eq451937
    | (have j0 := eq451937 X0
       grind)
    | exact resolve eq451937 eq378326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451937
  have eq452071 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq452070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452070
  have eq452094 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq452071 X0
       have i₂ := eq72951 X0
       grind)
    | exact superpose eq72951 eq452071
    | (have j0 := eq452071 X0
       grind)
    | exact resolve eq452071 eq72951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72951 eq452071
  have eq454246 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (k (M.op (k X0 X0) X0) (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq80159 X0 (k X0 X0)
       have i₂ := eq452094 X0
       grind)
    | exact superpose eq452094 eq80159
    | (have j0 := eq80159 X0 (k X0 X0)
       have j1 := eq452094 X0
       grind)
    | exact resolve eq80159 eq452094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80159 eq452094
  have eq454386 : ∀ X0 : G, (k X0 X0) = (k (M.op (k X0 X0) X0) (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq454246 X0
       have j1 := eq482 X0
       grind)
    | (have r₁ := eq454246 X0
       have r₂ := eq482 X0
       grind)
    | exact resolve eq454246 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454246
  have eq454423 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq454386 X0
       have i₂ := eq451611 X0
       grind)
    | exact superpose eq451611 eq454386
    | (have j0 := eq454386 X0
       grind)
    | exact resolve eq454386 eq451611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454386
  have eq454436 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq454423 X0
       have i₂ := eq378326 X0
       grind)
    | exact superpose eq378326 eq454423
    | (have j0 := eq454423 X0
       grind)
    | exact resolve eq454423 eq378326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378326 eq454423
  have eq454437 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq454436 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454436
  have eq455534 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq445183 (k X0 X0)
       have i₂ := eq454437 X0
       grind)
    | exact superpose eq454437 eq445183
    | (have j0 := eq445183 (k X0 X0)
       have j1 := eq454437 X0
       grind)
    | exact resolve eq445183 eq454437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445183 eq454437
  have eq455745 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq455534 X0
       have j1 := eq482 X0
       grind)
    | (have r₁ := eq455534 X0
       have r₂ := eq482 X0
       grind)
    | exact resolve eq455534 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq455534
  have eq455773 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq455745 X0
       have i₂ := eq451611 (k X0 X0)
       grind)
    | exact superpose eq451611 eq455745
    | (have j0 := eq455745 X0
       grind)
    | exact resolve eq455745 eq451611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451611 eq455745
  have eq464111 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (k X0 X0) (k X0 X0) x
       have i₂ := eq455773 X0
       grind)
    | exact superpose eq455773 eq64
    | (have j1 := eq455773 X0
       grind)
    | exact resolve eq64 eq455773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455773
  have eq464485 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq145744 X0
       have i₂ := eq464111 X0 X0
       grind)
    | exact superpose eq464111 eq145744
    | (have j0 := eq145744 X0
       have j1 := eq464111 X0 x
       grind)
    | exact resolve eq145744 eq464111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145744 eq464111
  have eq464804 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq464485 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464485
  have eq465486 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq464804 (σ X0)
       grind)
    | exact superpose eq464804 eq15
    | exact resolve eq15 eq464804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465610 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq465486 X0
       have i₂ := eq464804 X0
       grind)
    | exact superpose eq464804 eq465486
    | exact resolve eq465486 eq464804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465486
  have eq468109 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0) (σ X0)
       have i₂ := eq465610 X0
       grind)
    | exact superpose eq465610 eq68
    | exact resolve eq68 eq465610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq465610
  have eq1153633 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31233 X1 X2 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31233
  have eq1153634 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1153633 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153633
  have eq1154252 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq370547 X0
       have i₂ := eq1153634 X0 X0 X1
       grind)
    | exact superpose eq1153634 eq370547
    | (have j1 := eq1153634 X0 X0 X1
       grind)
    | exact resolve eq370547 eq1153634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370547 eq1153634
  have eq1154418 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1154252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154252
  have eq1155280 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X0 x
       have i₂ := eq1154418 X0 X1
       grind)
    | exact superpose eq1154418 eq64
    | (have j1 := eq1154418 X0 X2
       grind)
    | exact resolve eq64 eq1154418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155288 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq788 X0 X0 X2
       have i₂ := eq1154418 X0 X1
       grind)
    | exact superpose eq1154418 eq788
    | (have j1 := eq1154418 X0 X2
       grind)
    | exact resolve eq788 eq1154418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq1155557 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 (σ X0)
       have i₂ := eq1154418 (σ X0) X1
       grind)
    | exact superpose eq1154418 eq99
    | (have j1 := eq1154418 (σ X0) X1
       grind)
    | exact resolve eq99 eq1154418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1154418
  have eq1155703 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1155557 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155557
  have eq1155864 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1155703 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1155703
    | (have j0 := eq1155703 X0 X1
       grind)
    | exact resolve eq1155703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155703
  have eq1156084 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1155864 X0 X1
       have i₂ := eq464804 X0
       grind)
    | exact superpose eq464804 eq1155864
    | (have j0 := eq1155864 X0 X1
       grind)
    | exact resolve eq1155864 eq464804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464804 eq1155864
  have eq1157910 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X0 x
       have i₂ := eq1156084 X0 X1
       grind)
    | exact superpose eq1156084 eq64
    | (have j1 := eq1156084 X0 X2
       grind)
    | exact resolve eq64 eq1156084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1156084
  have eq1159810 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1155288 y (σ x) X0
       grind)
    | exact superpose eq1155288 eq16
    | (have j1 := eq1155288 y x X0
       grind)
    | exact resolve eq16 eq1155288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155288
  have eq1165570 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) ∨ (k X1 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1159810 X0
       have i₂ := eq1155280 y x X1
       grind)
    | exact superpose eq1155280 eq1159810
    | (have j0 := eq1159810 X0
       have j1 := eq1155280 y X1 X0
       grind)
    | exact resolve eq1159810 eq1155280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159810
  have eq1165575 : ∀ X0 X1 : G, (k X0 y) = (M.op X0 y) ∨ (k X1 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq1165570 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165570
  have eq1168041 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1165575 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165575
  have eq1168042 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1168041 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168041
  have eq1169106 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq119941 X0 X1
       have i₂ := eq1168042 x
       grind)
    | exact superpose eq1168042 eq119941
    | (have j0 := eq119941 X0 X1
       grind)
    | exact resolve eq119941 eq1168042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119941
  have eq1169107 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq1169106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169106
  have eq1171057 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq468109 y
       have i₂ := eq1169107 (σ (M.op y y)) X0
       grind)
    | (have i₁ := eq468109 y
       have i₂ := eq1169107 X0 (σ (M.op y y))
       grind)
    | exact superpose eq1169107 eq468109
    | exact resolve eq468109 eq1169107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171071 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1169107 (σ x) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq1169107 X0 (σ x)
       grind)
    | exact superpose eq1169107 eq16
    | exact resolve eq16 eq1169107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169107
  have eq1173183 : ∀ X0 X1 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (k X1 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1171071 X0
       have i₂ := eq1157910 y x X1
       grind)
    | exact superpose eq1157910 eq1171071
    | (have j1 := eq1157910 y X1 X1
       grind)
    | exact resolve eq1171071 eq1157910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157910
  have eq1173488 : ∀ X1 : G, (k X1 (σ y)) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have j0 := eq1173183 x X1
       have j1 := eq1155280 (σ y) X1 X1
       grind)
    | (have r₁ := eq1173183 X1 X1
       have r₂ := eq1155280 (σ y) X1 x
       grind)
    | exact resolve eq1173183 eq1155280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155280 eq1173183
  have eq1176605 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (M.op (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ y)
       have i₂ := eq1173488 (σ X0)
       grind)
    | exact superpose eq1173488 eq28
    | exact resolve eq28 eq1173488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1173488
  have eq1176955 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq1176605 X0
       have i₂ := eq1171057 (σ X0)
       grind)
    | exact superpose eq1171057 eq1176605
    | exact resolve eq1176605 eq1171057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171057 eq1176605
  have eq1177371 : ∀ X0 : G, (M.op y y) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1176955 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq1176955
    | exact resolve eq1176955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176955
  have eq1177619 : ∀ X0 : G, (M.op y y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1177371 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1177371
    | exact resolve eq1177371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177371
  have eq1177936 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1168042 X0
       have i₂ := eq1177619 X0
       grind)
    | exact superpose eq1177619 eq1168042
    | exact resolve eq1168042 eq1177619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168042 eq1177619
  have eq1179122 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1177936 X0
       have i₂ := eq1177936 X1
       grind)
    | (have i₁ := eq1177936 X0
       have i₂ := eq1177936 y
       grind)
    | exact superpose eq1177936 eq1177936
    | exact resolve eq1177936 eq1177936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177936
  have eq1181171 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq468109 y
       have i₂ := eq1179122 X0 y
       grind)
    | (have i₁ := eq468109 y
       have i₂ := eq1179122 y x
       grind)
    | exact superpose eq1179122 eq468109
    | exact resolve eq468109 eq1179122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468109
  have eq1181447 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1171071 X1
       have i₂ := eq1179122 X0 x
       grind)
    | (have i₁ := eq1171071 X1
       have i₂ := eq1179122 x X0
       grind)
    | exact superpose eq1179122 eq1171071
    | exact resolve eq1171071 eq1179122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171071 eq1179122
  have eq1181490 : False := by grind
  exact eq1181490

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq59 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq59 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq60 (σ X0)
       grind)
    | exact superpose eq60 eq15
    | exact resolve eq15 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq60 (τ X0)
       grind)
    | exact superpose eq60 eq18
    | exact resolve eq18 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq66 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65
    | exact resolve eq65 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq63
    | exact resolve eq63 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq66
    | exact resolve eq66 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq66
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq117 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ X0) x
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq21
    | exact resolve eq21 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq13
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq282 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 X1 X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq303 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq310 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq303 X0 X1
       have j1 := eq120 X1 X0
       grind)
    | (have r₁ := eq303 X0 X0
       have r₂ := eq120 X0 X1
       grind)
    | exact resolve eq303 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq303
  have eq387 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 (M.op X0 X1) X1
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq117
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq117
  have eq521 : ∀ X0 X1 X3 : G, (M.op (σ (M.op X0 X1)) X3) = (k X3 (σ (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq43 x (σ (M.op X0 X1)) x
       have i₂ := eq387 X0 X1 x
       grind)
    | exact superpose eq387 eq43
    | exact resolve eq43 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq864 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq310 (σ X1) X0
       grind)
    | exact superpose eq310 eq15
    | (have j1 := eq310 (σ X1) X0
       grind)
    | exact resolve eq15 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq887 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq864
    | (have j0 := eq864 X0 X1
       grind)
    | exact resolve eq864 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq864
  have eq1068 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) (σ X2)) = (σ (k X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op X0 X1)
       have i₂ := eq521 X0 X1 (σ X2)
       grind)
    | exact superpose eq521 eq15
    | exact resolve eq15 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq1081 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) (σ X2)) = (σ (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1068 X0 X1 X2
       have i₂ := eq43 X0 X1 X2
       grind)
    | exact superpose eq43 eq1068
    | exact resolve eq1068 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1068
  have eq2481 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq887 X0 (τ X1)
       grind)
    | exact superpose eq887 eq17
    | (have j1 := eq887 X0 (τ X1)
       grind)
    | exact resolve eq17 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq887
  have eq16403 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2481 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2481
    | exact resolve eq2481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq16594 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16403 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq16403
    | (have j0 := eq16403 X0 X1
       grind)
    | exact resolve eq16403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16403
  have eq18465 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq874 x y
       grind)
    | exact superpose eq874 eq16
    | (have j1 := eq874 x y
       grind)
    | exact resolve eq16 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18559 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq874 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq44023 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18465
       have i₂ := eq16594 y x
       grind)
    | exact superpose eq16594 eq18465
    | (have j1 := eq16594 y x
       grind)
    | (have r₁ := eq18465
       have r₂ := eq16594 y x
       grind)
    | exact resolve eq18465 eq16594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18465
  have eq44024 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq44023
  have eq44506 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq44024
       grind)
    | exact superpose eq44024 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq44024
       grind)
    | exact resolve eq13 eq44024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44024
  have eq44562 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq44506
  have eq1907884 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18559 x y
       have i₂ := eq44562
       grind)
    | exact superpose eq44562 eq18559
    | (have j0 := eq18559 x y
       grind)
    | exact resolve eq18559 eq44562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18559 eq44562
  have eq1908160 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1907884
  have eq1908161 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1908160
  have eq1908233 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1908161
       grind)
    | exact superpose eq1908161 eq16
    | exact resolve eq16 eq1908161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1908239 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq119 x (σ y)
       have i₂ := eq1908161
       grind)
    | exact superpose eq1908161 eq119
    | (have j0 := eq119 x (σ y)
       grind)
    | (have r₁ := eq119 x (σ y)
       have r₂ := eq1908161
       grind)
    | exact resolve eq119 eq1908161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq1908161
  have eq1908590 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1908239
  have eq1908724 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1908590
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1908590
    | exact resolve eq1908590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908590
  have eq2123806 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16594 y x
       have i₂ := eq1908724
       grind)
    | exact superpose eq1908724 eq16594
    | (have j0 := eq16594 y x
       grind)
    | exact resolve eq16594 eq1908724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16594 eq1908724
  have eq2124648 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2123806
       have r₂ := eq1908233
       grind)
    | exact resolve eq2123806 eq1908233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123806
  have eq2130190 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1908233
       have i₂ := eq2124648
       grind)
    | exact superpose eq2124648 eq1908233
    | exact resolve eq1908233 eq2124648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908233 eq2124648
  have eq2130507 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq2130190
  have eq2130508 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq2130507
  have eq2135883 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2130508
       grind)
    | exact superpose eq2130508 eq10
    | exact resolve eq10 eq2130508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130508
  have eq2136587 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2135883
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2135883
    | exact resolve eq2135883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135883
  have eq2136588 : x = (M.op x x) := by grind
  clear eq2136587
  have eq2137022 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1081 x x x
       have i₂ := eq2136588
       grind)
    | exact superpose eq2136588 eq1081
    | exact resolve eq1081 eq2136588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq2136588
  have eq2188344 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2137022 y
       grind)
    | exact superpose eq2137022 eq16
    | (have r₁ := eq16
       have r₂ := eq2137022 y
       grind)
    | exact resolve eq16 eq2137022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137022
  have eq2189313 : False := by grind
  exact eq2189313

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq21 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq53
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq102 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (M.op X0 X1)
       have i₂ := eq43 X0 X1 (τ X2)
       grind)
    | exact superpose eq43 eq17
    | exact resolve eq17 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq258 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq81 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq271 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq272 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq274 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq272 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq272 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq295 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op (τ X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (τ X1) X0 X1
       have i₂ := eq25 (τ X1) X0
       grind)
    | exact superpose eq25 eq102
    | exact resolve eq102 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq102
  have eq492 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq271 (M.op X0 X1)
       have i₂ := eq43 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq271
    | (have j0 := eq271 (M.op X0 X1)
       grind)
    | exact resolve eq271 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq501 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq492
    | (have j0 := eq492 X0 X1
       grind)
    | exact resolve eq492 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq502 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq513 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (k X2 (σ (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 (M.op X0 X1) X2
       have i₂ := eq43 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq274
    | (have j0 := eq274 (M.op X0 X1) X2
       grind)
    | exact resolve eq274 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq522 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (k X2 (σ (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq513 X0 X1 X2
       have i₂ := eq21 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq513
    | (have j0 := eq513 X0 X1 X2
       grind)
    | exact resolve eq513 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq523 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq522 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq544 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (M.op (σ (M.op (τ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X1 X0
       have i₂ := eq523 (τ X0) X1 X0
       grind)
    | exact superpose eq523 eq295
    | exact resolve eq295 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq552 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) (σ X2)) = (σ (k X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op X0 X1)
       have i₂ := eq523 X0 X1 (σ X2)
       grind)
    | exact superpose eq523 eq15
    | exact resolve eq15 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq564 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op X0 X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 X0 X1 X2
       have i₂ := eq43 X0 X1 X2
       grind)
    | exact superpose eq43 eq552
    | exact resolve eq552 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq620 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (σ (M.op X0 (τ (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2 (σ (M.op (τ (M.op X1 X2)) X0))
       have i₂ := eq544 (M.op X1 X2) X0
       grind)
    | exact superpose eq544 eq21
    | exact resolve eq21 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq664 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (τ (M.op X0 X1)))
       have i₂ := eq620 X2 X0 X1
       grind)
    | exact superpose eq620 eq10
    | exact resolve eq10 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 X3 : G, (σ (k (M.op X2 (τ (M.op X0 X1))) X3)) = (k (M.op X0 X1) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 (M.op X2 (τ (M.op X0 X1))) X3
       have i₂ := eq620 X2 X0 X1
       grind)
    | exact superpose eq620 eq15
    | exact resolve eq15 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 X3 : G, (M.op (τ (M.op X0 X1)) X3) = (k X3 (τ (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq43 x (τ (M.op X0 X1)) x
       have i₂ := eq664 X0 X1 x
       grind)
    | exact superpose eq664 eq43
    | exact resolve eq43 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq664
  have eq1280 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq258
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq258
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq258 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq1281 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1280
  have eq15028 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq82 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq15029 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq15028 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15028
  have eq15032 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15029 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15029
    | (have j0 := eq15029 X0
       grind)
    | exact resolve eq15029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15029
  have eq15084 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15032 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15032
    | exact resolve eq15032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15032
  have eq15210 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15084 X0
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq15084
    | (have j0 := eq15084 X0
       grind)
    | exact resolve eq15084 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq15084
  have eq15235 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq15210 X0
       grind)
    | exact superpose eq15210 eq11
    | (have j1 := eq15210 X0
       grind)
    | exact resolve eq11 eq15210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15210
  have eq15330 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15235 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq15235
    | (have j0 := eq15235 X0
       grind)
    | exact resolve eq15235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15235
  have eq15368 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15330 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq15330 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq15330 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15330
  have eq15476 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq15368 (σ X0)
       grind)
    | exact superpose eq15368 eq15
    | exact resolve eq15 eq15368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15543 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15476 X0
       have i₂ := eq15368 X0
       grind)
    | exact superpose eq15368 eq15476
    | exact resolve eq15476 eq15368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15476
  have eq26012 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq502 x y
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq502
    | exact resolve eq502 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq1281
  have eq26059 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq26012
  have eq26108 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26059
       have i₂ := eq15543 x
       grind)
    | exact superpose eq15543 eq26059
    | exact resolve eq26059 eq15543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15543 eq26059
  have eq93137 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq794 (σ x) (σ y) x
       have i₂ := eq26108
       grind)
    | exact superpose eq26108 eq794
    | exact resolve eq794 eq26108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq93238 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq93137 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq93137
    | exact resolve eq93137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93137
  have eq93268 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq93238 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq93238 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq93238 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93238
  have eq94808 : ∀ X0 : G, (M.op x x) = (τ (σ x)) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq93268 X0
       grind)
    | exact superpose eq93268 eq10
    | (have j1 := eq93268 X0
       grind)
    | exact resolve eq10 eq93268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93268
  have eq94987 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq94808 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq94808
    | (have j0 := eq94808 X0
       grind)
    | exact resolve eq94808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94808
  have eq95030 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq94987 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq94987 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq94987 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94987
  have eq95453 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) (σ x)) = (σ (M.op x (M.op X0 (τ (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq665 X1 X2 X0 x
       have i₂ := eq95030 (M.op X0 (τ (M.op X1 X2)))
       grind)
    | exact superpose eq95030 eq665
    | exact resolve eq665 eq95030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq95030
  have eq95543 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ (M.op X1 X2)))) = (k (M.op X1 X2) (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95453 X0 X1 X2
       have i₂ := eq21 X0 (τ (M.op X1 X2)) x
       grind)
    | exact superpose eq21 eq95453
    | exact resolve eq95453 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq95453
  have eq95589 : ∀ X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) (σ x)) := by
    intro X1 X2
    first
    | (have i₁ := eq95543 x X1 X2
       have i₂ := eq620 x X1 X2
       grind)
    | exact superpose eq620 eq95543
    | exact resolve eq95543 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq95543
  have eq97611 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq95589 (σ x) (σ y)
       have i₂ := eq26108
       grind)
    | exact superpose eq26108 eq95589
    | exact resolve eq95589 eq26108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26108 eq95589
  have eq97792 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97611
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq97611
    | exact resolve eq97611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97611
  have eq97856 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97792
       have i₂ := eq15368 x
       grind)
    | exact superpose eq15368 eq97792
    | exact resolve eq97792 eq15368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15368 eq97792
  have eq97857 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97856
  have eq104524 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq97857
       grind)
    | exact superpose eq97857 eq10
    | exact resolve eq10 eq97857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97857
  have eq104725 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq104524
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq104524
    | exact resolve eq104524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104524
  have eq104726 : x = (M.op x x) := by grind
  clear eq104725
  have eq105156 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq564 x x x
       have i₂ := eq104726
       grind)
    | exact superpose eq104726 eq564
    | exact resolve eq564 eq104726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq104726
  have eq114363 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105156 y
       grind)
    | exact superpose eq105156 eq16
    | (have r₁ := eq16
       have r₂ := eq105156 y
       grind)
    | exact resolve eq16 eq105156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105156
  have eq114567 : False := by grind
  exact eq114567

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq16 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 X1 x X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq181 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (M.op (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 x
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq179 (k X0 X0) X0 x
       grind)
    | exact superpose eq179 eq181
    | exact resolve eq181 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq196 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq179 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x y X0
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x) (σ y) X0
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X0 x
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq179
    | exact resolve eq179 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 x
       have i₂ := eq179 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq179 sF0 x x
       grind)
    | exact superpose eq179 eq175
    | exact resolve eq175 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq215 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq196 eq174
    | exact resolve eq174 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq221 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq197 eq174
    | exact resolve eq174 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq227 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq215 eq41
    | exact resolve eq41 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq215
  have eq228 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq227
    | exact resolve eq227 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq233 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op (M.op x y) x) y)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq208
       grind)
    | exact superpose eq208 eq16
    | exact resolve eq16 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (M.op x y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq233 x
       have i₂ := eq179 (M.op sF0 x) y x
       grind)
    | exact superpose eq179 eq233
    | exact resolve eq233 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq233
  have eq235 : (M.op x y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq234
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq234
    | exact resolve eq234 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq269 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq228 eq202
    | exact resolve eq202 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq452 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq540 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq452
    | exact resolve eq452 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq676 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (τ X0) X1
       have i₂ := eq540 X0 X0
       grind)
    | exact superpose eq540 eq202
    | exact resolve eq202 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq540
  have eq702 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (M.op x y) = (k y x) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq770 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq776 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq770
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq770
    | exact resolve eq770 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq781 : (k y y) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq765
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq765
    | exact resolve eq765 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq819 : (k y y) = (M.op (M.op x y) x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq781
       have i₂ := eq208
       grind)
    | exact superpose eq208 eq781
    | exact resolve eq781 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq1357 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq221 eq676
    | exact resolve eq676 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq676
  have eq2456 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq776 eq207
    | exact resolve eq207 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq2462 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2456
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq2456
    | exact resolve eq2456 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456
  have eq2468 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq2462
    | exact resolve eq2462 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq2527 : (M.op x y) = (M.op (k y y) y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq819 eq235
    | exact resolve eq235 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq2545 : (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq2527
       have i₂ := eq183 y
       grind)
    | exact superpose eq183 eq2527
    | exact resolve eq2527 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq12165 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2545
       grind)
    | exact superpose eq2545 eq40
    | exact resolve eq40 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq12166 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq2545
       grind)
    | exact superpose eq2545 eq183
    | exact resolve eq183 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2545
  have eq12181 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq12165
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12165
    | exact resolve eq12165 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12186 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq20 eq12181
    | exact resolve eq12181 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12800 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq12166
       grind)
    | exact superpose eq12166 eq39
    | exact resolve eq39 eq12166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12166
  have eq12803 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq12800
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12800
    | exact resolve eq12800 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12800
  have eq12807 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq12803
    | exact resolve eq12803 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12803
  have eq12836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq12186 eq2468
    | exact resolve eq2468 eq12186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468 eq12186
  have eq12859 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq12836
       have r₂ := eq27
       grind)
    | exact resolve eq12836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12836
  have eq12872 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq12859 eq114
    | exact resolve eq114 eq12859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq12859
  have eq12891 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ x = y := by grind
  have eq18865 : (k y y) ≠ (M.op (M.op x y) x) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq702 y x
       have i₂ := eq208
       grind)
    | exact superpose eq208 eq702
    | (have j0 := eq702 x y
       grind)
    | exact resolve eq702 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq18869 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq776 eq702
    | (have j0 := eq702 (σ x) (σ y)
       grind)
    | (have r₁ := eq702 (σ y) (σ x)
       have r₂ := eq776
       grind)
    | exact resolve eq702 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq776
  have eq18883 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq18869
  have eq18884 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq18883
  have eq19052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq12807 eq18884
    | exact resolve eq18884 eq12807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12807
  have eq19075 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19052
       have r₂ := eq27
       grind)
    | exact resolve eq19052 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19052
  have eq56071 : (k y y) ≠ (k y y) ∨ x = y ∨ y = (k y x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq819 eq18865
    | (have r₁ := eq18865
       have r₂ := eq819
       grind)
    | exact resolve eq18865 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq18865
  have eq56079 : (k y y) ≠ (k y y) ∨ x = y ∨ y = (k y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq56071
  have eq56080 : (M.op x y) = (k y x) ∨ y = (k y x) ∨ x = y := by grind
  clear eq56079
  have eq56686 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq56080
       have i₂ := eq12872
       grind)
    | exact superpose eq12872 eq56080
    | exact resolve eq56080 eq12872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12872 eq56080
  have eq56704 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by grind
  clear eq56686
  have eq56715 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq56704
       have r₂ := eq12891
       grind)
    | exact resolve eq56704 eq12891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12891 eq56704
  have eq56742 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq56715
       grind)
    | exact superpose eq56715 eq39
    | exact resolve eq39 eq56715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56715
  have eq56754 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq56742
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq56742
    | exact resolve eq56742 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56742
  have eq56761 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq56754
    | exact resolve eq56754 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56754
  have eq56806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56761 eq18884
    | exact resolve eq18884 eq56761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18884 eq56761
  have eq56848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq56806
  have eq56875 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq56848
       have r₂ := eq27
       grind)
    | exact resolve eq56848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56848
  have eq56891 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq56875 eq1357
    | exact resolve eq1357 eq56875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357 eq56875
  have eq57328 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19075
       have i₂ := eq56891 sF0
       grind)
    | exact superpose eq56891 eq19075
    | (have j1 := eq56891 x
       grind)
    | exact resolve eq19075 eq56891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19075 eq56891
  have eq57340 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq57328
  have eq57402 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq57340 eq31
    | exact resolve eq31 eq57340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57340
  have eq57607 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq57402
    | exact resolve eq57402 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq57402
  have eq57608 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq57607
  have eq57616 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57608 eq28
    | exact resolve eq28 eq57608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq57608
  have eq57834 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq57616
    | exact resolve eq57616 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq57616
  have eq57835 : y = (M.op x y) ∨ x = y := by grind
  clear eq57834
  have eq57856 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq57835
       grind)
    | exact superpose eq57835 eq24
    | exact resolve eq24 eq57835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57835
  have eq57961 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq57856
    | exact resolve eq57856 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57856
  have eq58034 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq57961 eq269
    | exact resolve eq269 eq57961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq58433 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq58034 eq26
    | (have j1 := eq58034 (σ x)
       grind)
    | exact resolve eq26 eq58034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58034
  have eq58474 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq58433 eq27
    | exact resolve eq27 eq58433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58433
  have eq58726 : x = y := by
    first
    | (have r₁ := eq58474
       have r₂ := eq57961
       grind)
    | exact resolve eq58474 eq57961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57961 eq58474
  have eq59163 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq58726
       grind)
    | exact superpose eq58726 eq18
    | exact resolve eq18 eq58726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq59164 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq58726
       grind)
    | exact superpose eq58726 eq24
    | exact resolve eq24 eq58726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq58726
  have eq59255 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq59164
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59164
    | exact resolve eq59164 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59164
  have eq59256 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq59163
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq59163
    | exact resolve eq59163 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59163
  have eq59257 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59255 eq26
    | exact resolve eq26 eq59255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq59255
  have eq59445 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq59257
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq59257
    | exact resolve eq59257 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq59257
  have eq59458 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq59256
       grind)
    | exact superpose eq59256 eq39
    | exact resolve eq39 eq59256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq59256
  have eq59484 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq59458
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59458
    | exact resolve eq59458 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq59458
  have eq59493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59445 eq59484
    | exact resolve eq59484 eq59445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59445 eq59484
  have eq59501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq59493
    | exact resolve eq59493 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq59493
  have eq59507 : False := by grind
  exact eq59507
