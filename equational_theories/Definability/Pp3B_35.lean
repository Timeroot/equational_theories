import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_y_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq13 (k X0 (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq13
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq153 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq153
    | exact resolve eq153 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq175
  have eq268 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq32 eq247
    | exact resolve eq247 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq690 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 (M.op X1 X1)
       have r₂ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq753 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq761 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq776 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq727 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq795 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq776 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq776 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq776 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq776 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq826 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq762 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq762
    | (have j0 := eq762 (σ X0)
       grind)
    | exact resolve eq762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq937 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq795 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq795
    | (have j0 := eq795 (σ X0) X1
       grind)
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq690 X0 x x X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq690
    | exact resolve eq690 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1228 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1168
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq1168 X0
       grind)
    | exact superpose eq1168 eq16
    | exact resolve eq16 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq1168 X0
       grind)
    | exact superpose eq1168 eq16
    | exact resolve eq16 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1241 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1822 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq41
    | exact resolve eq41 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq744
  have eq1823 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1822
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1822
    | exact resolve eq1822 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1822
  have eq1825 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1823
    | exact resolve eq1823 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq1921 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq1234
    | exact resolve eq1234 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq2166 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X1)
       have i₂ := eq1921 X0 X1
       grind)
    | exact superpose eq1921 eq11
    | (have j0 := eq11 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq11 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2206 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2166 X0 X1
       have j1 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq2166 X1 X1
       have r₂ := eq13 (k X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq2166 X1 X1
       have r₂ := eq13 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq2166 X0 X1
       have r₂ := eq13 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq2166 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq2208 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2206 X0 X1
       have j1 := eq28 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq2206 X0 X1
       have r₂ := eq28 X0 (M.op X0 X1)
       grind)
    | exact resolve eq2206 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2206
  have eq2302 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (k y (τ (M.op (σ y) X0))) := by
    intro X0
    first
    | (have i₁ := eq108 (M.op sF3 x)
       have i₂ := eq2208 sF3 x
       grind)
    | exact superpose eq2208 eq108
    | exact resolve eq108 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1825 eq753
    | exact resolve eq753 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40638 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq40627
       have r₂ := eq27
       grind)
    | exact resolve eq40627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40627
  have eq40647 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40638 eq2302
    | exact resolve eq2302 eq40638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40638
  have eq40729 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq40647
    | exact resolve eq40647 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40647
  have eq40735 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq40729
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq40729
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq40729
       have r₂ := eq13 x y
       grind)
    | exact resolve eq40729 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40729
  have eq40742 : y = (k (τ (σ x)) y) ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40735 eq268
    | exact resolve eq268 eq40735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq40735
  have eq40831 : y = (k (τ (σ x)) y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq795 y (τ (σ x))
       grind)
    | (have r₁ := eq40742
       have r₂ := eq795 y x
       grind)
    | exact resolve eq40742 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq40742
  have eq40836 : y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq40831
    | exact resolve eq40831 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40831
  have eq40837 : y = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq40836
       have r₂ := eq13 x y
       grind)
    | exact resolve eq40836 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40836
  have eq40843 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq40837
       grind)
    | exact superpose eq40837 eq36
    | exact resolve eq36 eq40837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq40837
  have eq40849 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq40843
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40843
    | exact resolve eq40843 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40843
  have eq40855 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40849 eq1825
    | exact resolve eq1825 eq40849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq40858 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40849 eq753
    | exact resolve eq753 eq40849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq40849
  have eq41632 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2208 y y
       have i₂ := eq40855
       grind)
    | exact superpose eq40855 eq2208
    | exact resolve eq2208 eq40855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208 eq40855
  have eq41676 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40858 eq2302
    | exact resolve eq2302 eq40858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302 eq40858
  have eq41757 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq41676
    | exact resolve eq41676 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41676
  have eq42724 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq937 y X0
       have i₂ := eq41632
       grind)
    | exact superpose eq41632 eq937
    | (have j0 := eq937 y X0
       grind)
    | exact resolve eq937 eq41632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq41632
  have eq42738 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq42724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42724
  have eq42744 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq42738 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42738
    | (have j0 := eq42738 X0
       grind)
    | exact resolve eq42738 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42738
  have eq43186 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq41757 eq1168
    | exact resolve eq1168 eq41757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41757
  have eq43272 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq26 eq43186
    | exact resolve eq43186 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43186
  have eq43273 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43272
  have eq43300 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq826 y
       have i₂ := eq43273
       grind)
    | exact superpose eq43273 eq826
    | (have j0 := eq826 y
       grind)
    | exact resolve eq826 eq43273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq43305 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1241 y
       have i₂ := eq43273
       grind)
    | exact superpose eq43273 eq1241
    | (have j0 := eq1241 y
       grind)
    | exact resolve eq1241 eq43273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43273
  have eq43315 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43305
  have eq43318 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43300
  have eq43331 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43318
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43318
    | exact resolve eq43318 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43318
  have eq43366 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq43315
       grind)
    | exact superpose eq43315 eq16
    | exact resolve eq16 eq43315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43367 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq43315
       grind)
    | exact superpose eq43315 eq16
    | exact resolve eq16 eq43315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43315
  have eq43421 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43366 X0
       have i₂ := eq1921 y X0
       grind)
    | exact superpose eq1921 eq43366
    | exact resolve eq43366 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43366
  have eq43721 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43331 eq16
    | exact resolve eq16 eq43331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43722 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43331 eq16
    | exact resolve eq16 eq43331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43331
  have eq43777 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43721 x
       have i₂ := eq1921 sF3 x
       grind)
    | exact superpose eq1921 eq43721
    | exact resolve eq43721 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43721
  have eq44805 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43367 X0
       have i₂ := eq43421 X0
       grind)
    | exact superpose eq43421 eq43367
    | exact resolve eq43367 eq43421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43367 eq43421
  have eq44912 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq44805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44805
  have eq45158 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 y X0
       have i₂ := eq44912 X0
       grind)
    | exact superpose eq44912 eq16
    | exact resolve eq16 eq44912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45289 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq44912 eq45158
    | exact resolve eq45158 eq44912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44912 eq45158
  have eq56987 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43722 eq45289
    | exact resolve eq45289 eq43722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43722 eq45289
  have eq57032 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq56987 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56987
  have eq57046 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43777 eq57032
    | exact resolve eq57032 eq43777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43777 eq57032
  have eq57737 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57046 eq26
    | (have j1 := eq57046 (σ x)
       grind)
    | exact resolve eq26 eq57046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq57046
  have eq57806 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57737
  have eq57834 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq57806 eq27
    | exact resolve eq27 eq57806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57806
  have eq65263 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq42744 eq108
    | exact resolve eq108 eq42744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq42744
  have eq65274 : (τ (σ y)) = (k y (τ (σ y))) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq65263
       have r₂ := eq57834
       grind)
    | exact resolve eq65263 eq57834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65263
  have eq65321 : y = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq65274
    | exact resolve eq65274 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq65274
  have eq65390 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1241 y
       have i₂ := eq65321
       grind)
    | exact superpose eq65321 eq1241
    | (have j0 := eq1241 y
       grind)
    | exact resolve eq1241 eq65321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241 eq65321
  have eq65400 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq65390
  have eq65591 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq65400
       grind)
    | exact superpose eq65400 eq16
    | exact resolve eq16 eq65400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65592 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq65400
       grind)
    | exact superpose eq65400 eq16
    | exact resolve eq16 eq65400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65400
  have eq65649 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65591 X0
       have i₂ := eq1921 y X0
       grind)
    | exact superpose eq1921 eq65591
    | exact resolve eq65591 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921 eq65591
  have eq83860 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65592 X0
       have i₂ := eq65649 X0
       grind)
    | exact superpose eq65649 eq65592
    | exact resolve eq65592 eq65649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65592 eq65649
  have eq84015 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq83860 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83860
  have eq84289 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1168 y
       have i₂ := eq84015 X0
       grind)
    | exact superpose eq84015 eq1168
    | (have j1 := eq84015 X0
       grind)
    | exact resolve eq1168 eq84015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq84015
  have eq84382 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq84289 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84289
    | (have j0 := eq84289 X0
       grind)
    | exact resolve eq84289 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84289
  have eq84556 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1233 y X0
       have i₂ := eq84382 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq84382 eq1233
    | exact resolve eq1233 eq84382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq84666 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq84382 eq84556
    | exact resolve eq84556 eq84382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84556
  have eq84752 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f84752_13 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f84752_14 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f84752_24 : y ≠ (M.op x y) := by grind
    have f84752_26 : ∀ X0 : G, (M.op y X0) = X0 := by
      intro X0
      first
      | (have j0 := f84752_14 X0
         grind)
      | (have r₁ := f84752_14 X0
         have r₂ := f84752_24
         grind)
      | exact resolve f84752_14 f84752_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f84752_27 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
      intro X0
      first
      | (have j0 := f84752_13 X0
         grind)
      | (have r₁ := f84752_13 X0
         have r₂ := f84752_24
         grind)
      | exact resolve f84752_13 f84752_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f84752_28 : ∀ X0 : G, y = (M.op X0 y) := by
      intro X0
      first
      | (have i₁ := f84752_27 X0
         have i₂ := f84752_26 X0
         grind)
      | exact superpose f84752_26 f84752_27
      | exact resolve f84752_27 f84752_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f84752_30 : y ≠ y := by
      first
      | (have i₁ := f84752_24
         have i₂ := f84752_28 x
         grind)
      | exact superpose f84752_28 f84752_24
      | (have r₁ := f84752_24
         have r₂ := f84752_28 x
         grind)
      | exact resolve f84752_24 f84752_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f84752_31 : False := by grind
    exact f84752_31
  clear eq84382 eq84666
  have eq85646 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq84752 x
       grind)
    | exact superpose eq84752 eq18
    | (have j1 := eq84752 x
       grind)
    | exact resolve eq18 eq84752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq84752
  have eq85825 : y = (M.op x y) := by grind
  clear eq85646
  have eq85855 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq85825
       grind)
    | exact superpose eq85825 eq24
    | exact resolve eq24 eq85825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq85825
  have eq86151 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq85855 eq20
    | exact resolve eq20 eq85855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq85855
  have eq86334 : False := by grind
  exact eq86334

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
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
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq76
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq82
    | exact resolve eq82 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq113 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq154 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq201 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq206 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq28 eq49
    | (have j0 := eq49 (σ y)
       grind)
    | exact resolve eq49 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq370 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq376 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq370 X0
       grind)
    | exact superpose eq370 eq14
    | exact resolve eq14 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq857 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq51 eq376
    | exact resolve eq376 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq859 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52 eq376
    | exact resolve eq376 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq376
  have eq3568 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq521 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq521
    | (have j0 := eq521 (τ X0)
       grind)
    | exact resolve eq521 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3575 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3568 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3568
    | (have j0 := eq3568 X0
       grind)
    | exact resolve eq3568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq3581 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3575 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3575
    | (have j0 := eq3575 X0
       grind)
    | exact resolve eq3575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3575
  have eq7508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq7508
    | exact resolve eq7508 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7508
  have eq7520 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq7509
       have r₂ := eq29
       grind)
    | exact resolve eq7509 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7509
  have eq7524 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq7520 eq370
    | exact resolve eq370 eq7520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7525 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq7520
  have eq7542 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq7524
    | exact resolve eq7524 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7524
  have eq7546 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7542
  have eq7592 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq7546
       grind)
    | exact superpose eq7546 eq46
    | exact resolve eq46 eq7546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq7546
  have eq7608 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7592
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7592
    | exact resolve eq7592 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7592
  have eq7759 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7608 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq7608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7608
  have eq7760 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7759
  have eq7764 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq7760
    | exact resolve eq7760 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7760
  have eq7780 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq7525 eq83
    | exact resolve eq83 eq7525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq7525
  have eq7789 : x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq7780
  have eq7803 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq370 y
       have i₂ := eq7789
       grind)
    | exact superpose eq7789 eq370
    | exact resolve eq370 eq7789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7789
  have eq7821 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7803
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq7803
    | exact resolve eq7803 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7803
  have eq7823 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7821 eq31
    | exact resolve eq31 eq7821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7821
  have eq7942 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq7823
    | exact resolve eq7823 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7823
  have eq7943 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq7942
  have eq8061 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq7943 eq30
    | exact resolve eq30 eq7943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8183 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq8061
    | exact resolve eq8061 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq8184 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8183 eq22
    | exact resolve eq22 eq8183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8183
  have eq8312 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8184
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq8184
    | exact resolve eq8184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8184
  have eq53111 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7764 eq370
    | exact resolve eq370 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq7764
  have eq53166 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq53111
    | exact resolve eq53111 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53111
  have eq53167 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq53166
  have eq53169 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq53167 eq29
    | exact resolve eq29 eq53167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53167
  have eq53222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8312 eq53169
    | (have r₁ := eq53169
       have r₂ := eq8312
       grind)
    | exact resolve eq53169 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53169
  have eq53223 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq53222
  have eq53224 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq53223
  have eq53230 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53224 eq206
    | exact resolve eq206 eq53224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq53255 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53224 eq859
    | exact resolve eq859 eq53224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq53224
  have eq53662 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53255 eq53230
    | exact resolve eq53230 eq53255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53230 eq53255
  have eq53713 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq53662
  have eq53717 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq53713
    | exact resolve eq53713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53713
  have eq53719 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53717 eq29
    | exact resolve eq29 eq53717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53717
  have eq53776 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq53719
       have r₂ := eq8312
       grind)
    | exact resolve eq53719 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8312 eq53719
  have eq53778 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53776 eq30
    | exact resolve eq30 eq53776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq53776
  have eq53996 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq53778
    | exact resolve eq53778 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53778
  have eq53997 : x = (M.op x y) ∨ x = y := by grind
  clear eq53996
  have eq53999 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq53997 eq22
    | exact resolve eq22 eq53997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54090 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq53997 eq857
    | exact resolve eq857 eq53997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq54208 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq53999
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53999
    | exact resolve eq53999 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53999
  have eq54447 : x = (k x x) ∨ x = y := by grind
  clear eq54090
  have eq54690 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq54447
       grind)
    | exact superpose eq54447 eq45
    | exact resolve eq45 eq54447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq54447
  have eq54737 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq54690
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54690
    | exact resolve eq54690 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54690
  have eq54847 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq54208 eq54737
    | exact resolve eq54737 eq54208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54208 eq54737
  have eq54914 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq54847
  have eq55069 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq54914 eq154
    | exact resolve eq154 eq54914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq54914
  have eq55123 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq32 eq55069
    | exact resolve eq55069 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq55069
  have eq55231 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq55123 eq3581
    | (have j0 := eq3581 (M.op x y)
       grind)
    | (have r₁ := eq3581 (M.op x y)
       have r₂ := eq55123
       grind)
    | exact resolve eq3581 eq55123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3581 eq55123
  have eq55236 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq55231
  have eq55312 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq55236 eq201
    | exact resolve eq201 eq55236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq55236
  have eq55399 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq53997 eq55312
    | exact resolve eq55312 eq53997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55312
  have eq55452 : y = (M.op x y) ∨ x = y := by grind
  clear eq55399
  have eq55454 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq55452
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq55452
    | exact resolve eq55452 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55452
  have eq55591 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq55454 eq53997
    | exact resolve eq53997 eq55454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53997 eq55454
  have eq55600 : x = y := by grind
  clear eq55591
  have eq55707 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq55600
       grind)
    | exact superpose eq55600 eq20
    | exact resolve eq20 eq55600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq55708 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq55600
       grind)
    | exact superpose eq55600 eq26
    | exact resolve eq26 eq55600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq55600
  have eq55856 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq55708
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55708
    | exact resolve eq55708 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55708
  have eq55859 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq55856 eq28
    | exact resolve eq28 eq55856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq55856
  have eq56078 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq55707
       grind)
    | exact superpose eq55707 eq68
    | exact resolve eq68 eq55707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq56096 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq55707
  have eq56149 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq56078
    | exact resolve eq56078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56078
  have eq56225 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq57530 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq57554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55859 eq57530
    | exact resolve eq57530 eq55859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57530
  have eq57569 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq57554
       have r₂ := eq29
       grind)
    | exact resolve eq57554 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57554
  have eq57574 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55859 eq57569
    | exact resolve eq57569 eq55859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57569
  have eq57581 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57574 eq29
    | exact resolve eq29 eq57574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57630 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57574 eq56225
    | exact resolve eq56225 eq57574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56225 eq57574
  have eq58156 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57630 eq56149
    | exact resolve eq56149 eq57630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56149 eq57630
  have eq58182 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq58156
  have eq58197 : x = (M.op x y) := by
    first
    | (have r₁ := eq58182
       have r₂ := eq57581
       grind)
    | exact resolve eq58182 eq57581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57581 eq58182
  have eq58222 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq58197 eq22
    | exact resolve eq22 eq58197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq58344 : x = (k x x) := by
    first
    | exact superpose eq58197 eq56096
    | exact resolve eq56096 eq58197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56096 eq58197
  have eq58450 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq58222
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58222
    | exact resolve eq58222 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58222
  have eq60405 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq521 x
       have i₂ := eq58344
       grind)
    | exact superpose eq58344 eq521
    | (have j0 := eq521 x
       grind)
    | exact resolve eq521 eq58344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq58344
  have eq60415 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq60405
  have eq60425 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60415
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq60415
    | exact resolve eq60415 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq60415
  have eq60446 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55859 eq60425
    | exact resolve eq60425 eq55859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55859 eq60425
  have eq60464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58450 eq60446
    | exact resolve eq60446 eq58450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58450 eq60446
  have eq60481 : False := by grind
  exact eq60481

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  clear eq22
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq67 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq51
    | exact resolve eq51 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq51
    | exact resolve eq51 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x x
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq9
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq9 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq67
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq67 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq305 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq306 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq310 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq383 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq306 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq306
    | (have j0 := eq306 (τ X0)
       grind)
    | exact resolve eq306 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq393 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq383
    | (have j0 := eq383 X0
       grind)
    | exact resolve eq383 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq400 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq393
    | (have j0 := eq393 X0
       grind)
    | exact resolve eq393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq405 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq400 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq400
    | (have j0 := eq400 (τ X0)
       grind)
    | exact resolve eq400 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq649 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1586 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq310 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1628 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1586 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1586
    | (have j0 := eq1586 X0
       grind)
    | exact resolve eq1586 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1586
  have eq1638 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1628 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1628
    | (have j0 := eq1628 X0
       grind)
    | exact resolve eq1628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq5553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq287
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq287
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq287 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq5556 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq5553
  have eq6137 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq288 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq288
    | (have j0 := eq288 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq288 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq288
  have eq6247 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6137 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6137
    | (have j0 := eq6137 X0 X0 X2
       grind)
    | exact resolve eq6137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6137
  have eq6254 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6247 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6247
    | (have j0 := eq6247 X0 X0 X2
       grind)
    | exact resolve eq6247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6247
  have eq6255 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6254 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6254
    | (have j0 := eq6254 X0 X0 X2
       grind)
    | exact resolve eq6254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254
  have eq6256 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6255 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6255
    | (have j0 := eq6255 X0 X1 X2
       grind)
    | exact resolve eq6255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6255
  have eq6257 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6256 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6256
    | (have j0 := eq6256 X0 X1 X2
       grind)
    | exact resolve eq6256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6256
  have eq12055 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (k X1 X0) X0) (k X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 (k X1 X0) X1 X0
       have i₂ := eq6257 X1 X0 (k X1 X0)
       grind)
    | exact superpose eq6257 eq91
    | (have j1 := eq6257 X1 X1 x
       grind)
    | exact resolve eq91 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq6257
  have eq19423 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5556
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq5556
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq5556
       grind)
    | exact resolve eq12 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19543 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19423 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19423
  have eq25832 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12055 X0 X0
       have i₂ := eq1638 X0
       grind)
    | exact superpose eq1638 eq12055
    | (have j0 := eq12055 X0 X0
       have j1 := eq1638 X0
       grind)
    | exact resolve eq12055 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq12055
  have eq25964 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25832
  have eq25967 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25964 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq25964
    | (have j0 := eq25964 (σ X0)
       grind)
    | exact resolve eq25964 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25964
  have eq203497 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ (M.op X1 X1) = (k X1 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq19543 X1
       grind)
    | exact superpose eq19543 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq19543 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq19543 X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq19543 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq19543 X0
       grind)
    | exact resolve eq12 eq19543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203779 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq203497 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203497
  have eq209808 : ∀ X0 : G, (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq405 (σ y)
       have i₂ := eq203779 X0 (σ y)
       grind)
    | exact superpose eq203779 eq405
    | (have j0 := eq405 (σ y)
       have j1 := eq203779 X0 x
       grind)
    | exact resolve eq405 eq203779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203779
  have eq210210 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq209808 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq209808
    | (have j0 := eq209808 X0
       grind)
    | exact resolve eq209808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209808
  have eq210322 : ∀ X0 : G, y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq210210 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq210210
    | (have j0 := eq210210 X0
       grind)
    | exact resolve eq210210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210210
  have eq210323 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq210322 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210322
  have eq214927 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq210323 X0
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq210323
    | (have j0 := eq210323 X0
       grind)
    | exact resolve eq210323 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210323
  have eq214936 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq214927 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214927
  have eq214940 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq214936 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq214936 X0
       have r₂ := eq12 X0 y
       grind)
    | (have r₁ := eq214936 X0
       have r₂ := eq12 X0 x
       grind)
    | (have r₁ := eq214936 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq214936 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214936
  have eq214941 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq214940 X0
       grind)
    | (have r₁ := eq214940 X0
       have r₂ := eq10 y
       grind)
    | exact resolve eq214940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214940
  have eq216297 : (τ (M.op (σ x) (σ x))) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq405 (σ x)
       have i₂ := eq214941 (σ x)
       grind)
    | exact superpose eq214941 eq405
    | (have j0 := eq405 (σ x)
       grind)
    | exact resolve eq405 eq214941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214941
  have eq216705 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq216297
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq216297
    | exact resolve eq216297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216297
  have eq216818 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq216705
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq216705
    | exact resolve eq216705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216705
  have eq216819 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq216818
  have eq218506 : ∀ X0 : G, x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq216819
       have i₂ := eq19543 X0
       grind)
    | exact superpose eq19543 eq216819
    | (have j1 := eq19543 X0
       grind)
    | exact resolve eq216819 eq19543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19543
  have eq218515 : ∀ X0 : G, x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq218506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218506
  have eq218519 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq218515 X0
       grind)
    | (have r₁ := eq218515 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq218515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218515
  have eq219885 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq405 (σ y)
       have i₂ := eq218519 (σ y)
       grind)
    | exact superpose eq218519 eq405
    | (have j0 := eq405 (σ y)
       grind)
    | exact resolve eq405 eq218519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq218519
  have eq220294 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq219885
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq219885
    | exact resolve eq219885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219885
  have eq220407 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq220294
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq220294
    | exact resolve eq220294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220294
  have eq220408 : y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq220407
  have eq220853 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq220408
       have i₂ := eq5556
       grind)
    | exact superpose eq5556 eq220408
    | exact resolve eq220408 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556 eq220408
  have eq220862 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq220853
  have eq220866 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq220862
       have r₂ := eq10 y
       grind)
    | exact resolve eq220862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220862
  have eq220868 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq216819
       have i₂ := eq220866
       grind)
    | exact superpose eq220866 eq216819
    | exact resolve eq216819 eq220866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216819 eq220866
  have eq221162 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq220868
  have eq221273 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq221162
       have r₂ := eq10 x
       grind)
    | exact resolve eq221162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221162
  have eq221287 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq221273
       grind)
    | exact superpose eq221273 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq221273
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq221273
       grind)
    | exact resolve eq12 eq221273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221292 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq221273
       grind)
    | exact superpose eq221273 eq73
    | exact resolve eq73 eq221273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221405 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq649 y y x
       have i₂ := eq221273
       grind)
    | exact superpose eq221273 eq649
    | exact resolve eq649 eq221273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221579 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq221287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221287
  have eq221648 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq221405 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq221405
    | exact resolve eq221405 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221405
  have eq224387 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq306 y
       have i₂ := eq221579 y
       grind)
    | exact superpose eq221579 eq306
    | (have j0 := eq306 y
       grind)
    | exact resolve eq306 eq221579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq221579
  have eq225784 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq221292 X0
       have i₂ := eq221648 X0
       grind)
    | exact superpose eq221648 eq221292
    | exact resolve eq221292 eq221648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221292 eq221648
  have eq226285 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq225784 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225784
  have eq226324 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq226285 X1
       grind)
    | exact superpose eq226285 eq73
    | (have j1 := eq226285 X1
       grind)
    | exact resolve eq73 eq226285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226437 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq649 x x x
       have i₂ := eq226285 X0
       grind)
    | exact superpose eq226285 eq649
    | (have j1 := eq226285 X1
       grind)
    | exact resolve eq649 eq226285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226285
  have eq226683 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq226437 X0 X1
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq226437
    | (have j0 := eq226437 X0 X1
       grind)
    | exact resolve eq226437 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226437
  have eq234347 : ∀ X0 X1 X2 : G, (M.op y X2) = X2 ∨ (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq226324 X0 X2
       have i₂ := eq226683 X0 X1
       grind)
    | exact superpose eq226683 eq226324
    | (have j0 := eq226324 X0 X2
       have j1 := eq226683 X0 X2
       grind)
    | exact resolve eq226324 eq226683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226324 eq226683
  have eq260882 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq234347 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234347
  have eq260883 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq260882 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260882
  have eq260914 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq260883 y X1
       grind)
    | exact superpose eq260883 eq74
    | (have j1 := eq260883 X0 X1
       grind)
    | exact resolve eq74 eq260883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq261767 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq260914 X0 X1
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq260914
    | (have j0 := eq260914 X0 X1
       grind)
    | exact resolve eq260914 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260914
  have eq265121 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq261767 X0 X1
       have i₂ := eq260883 X0 X2
       grind)
    | exact superpose eq260883 eq261767
    | (have j0 := eq261767 X0 X1
       have j1 := eq260883 X0 X1
       grind)
    | exact resolve eq261767 eq260883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260883 eq261767
  have eq317898 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq265121 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265121
  have eq317899 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq317898 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317898
  have eq318311 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq317899 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317899
  have eq318312 : y = (M.op x y) := by grind
  clear eq318311
  have eq1494424 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq224387
       have i₂ := eq221273
       grind)
    | exact superpose eq221273 eq224387
    | exact resolve eq224387 eq221273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221273 eq224387
  have eq1494438 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1494424
  have eq1494439 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1494438
  have eq1494454 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 (σ y) X0
       have i₂ := eq1494439
       grind)
    | exact superpose eq1494439 eq73
    | exact resolve eq73 eq1494439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1494598 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq649 (σ y) (σ y) x
       have i₂ := eq1494439
       grind)
    | exact superpose eq1494439 eq649
    | exact resolve eq649 eq1494439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494439
  have eq1495482 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1494598 X0
       have i₂ := eq94 (σ y) X0
       grind)
    | exact superpose eq94 eq1494598
    | exact resolve eq1494598 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494598
  have eq1629659 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1494454 X0
       have i₂ := eq1495482 X0
       grind)
    | exact superpose eq1495482 eq1494454
    | exact resolve eq1494454 eq1495482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494454
  have eq1630961 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1629659 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629659
  have eq1631015 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1495482 X0
       have i₂ := eq1630961 X0
       grind)
    | exact superpose eq1630961 eq1495482
    | exact resolve eq1495482 eq1630961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495482 eq1630961
  have eq1633392 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1631015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631015
  have eq1638000 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1633392 (σ x)
       grind)
    | exact superpose eq1633392 eq16
    | exact resolve eq16 eq1633392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633392
  have eq1638521 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1638000
       have i₂ := eq318312
       grind)
    | exact superpose eq318312 eq1638000
    | exact resolve eq1638000 eq318312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638000
  have eq1638522 : x = (M.op x x) := by grind
  clear eq1638521
  have eq1638707 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1638522
       grind)
    | exact superpose eq1638522 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1638522
       grind)
    | exact resolve eq12 eq1638522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1638712 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq1638522
       grind)
    | exact superpose eq1638522 eq73
    | exact resolve eq73 eq1638522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1638839 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq649 x x x
       have i₂ := eq1638522
       grind)
    | exact superpose eq1638522 eq649
    | exact resolve eq649 eq1638522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1639410 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1638707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638707
  have eq1639665 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1638839 X0
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq1638839
    | exact resolve eq1638839 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1638839
  have eq1639844 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 x) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq1639410 X0
       grind)
    | exact superpose eq1639410 eq73
    | exact resolve eq73 eq1639410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1643938 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25967 x
       have i₂ := eq1639410 x
       grind)
    | exact superpose eq1639410 eq25967
    | (have j0 := eq25967 x
       grind)
    | exact resolve eq25967 eq1639410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25967
  have eq1644482 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1643938
       have i₂ := eq1638522
       grind)
    | exact superpose eq1638522 eq1643938
    | exact resolve eq1643938 eq1638522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638522 eq1643938
  have eq1644483 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1644482
  have eq1645274 : (σ x) = (k (σ x) x) := by
    first
    | (have i₁ := eq1644483
       have i₂ := eq1639410 (σ x)
       grind)
    | exact superpose eq1639410 eq1644483
    | exact resolve eq1644483 eq1639410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639410 eq1644483
  have eq1675070 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1638712 X0
       have i₂ := eq1639665 X0
       grind)
    | exact superpose eq1639665 eq1638712
    | exact resolve eq1638712 eq1639665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638712 eq1639665
  have eq1675419 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq649 x X1 X0
       have i₂ := eq1675070 X0
       grind)
    | exact superpose eq1675070 eq649
    | exact resolve eq649 eq1675070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq1678540 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1675419 X0 X0
       have i₂ := eq1675070 X0
       grind)
    | exact superpose eq1675070 eq1675419
    | exact resolve eq1675419 eq1675070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675070 eq1675419
  have eq1849752 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1639844 (σ x) X0
       have i₂ := eq1645274
       grind)
    | exact superpose eq1645274 eq1639844
    | exact resolve eq1639844 eq1645274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639844 eq1645274
  have eq1850901 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1849752 X0
       have i₂ := eq1678540 X0 (σ x)
       grind)
    | exact superpose eq1678540 eq1849752
    | exact resolve eq1849752 eq1678540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678540 eq1849752
  have eq1856704 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1850901 (σ y)
       grind)
    | exact superpose eq1850901 eq16
    | exact resolve eq16 eq1850901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850901
  have eq1859686 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1856704
       have i₂ := eq318312
       grind)
    | exact superpose eq318312 eq1856704
    | exact resolve eq1856704 eq318312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318312 eq1856704
  have eq1859687 : False := by grind
  exact eq1859687

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_y_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  clear eq17
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq39
    | exact resolve eq39 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq88
    | (have j0 := eq88 (σ X0)
       grind)
    | exact resolve eq88 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq353 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq182 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq182 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq182 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq182 X0 X1
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq384 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq387 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq384
    | (have j0 := eq384 X0 X1
       grind)
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq585 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq661 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq67
    | (have j1 := eq123 X0
       grind)
    | exact resolve eq67 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq679 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq123 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1740 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq182 (k X0 X0) X0
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq182
    | (have j0 := eq182 X0 X0
       have j1 := eq661 X0
       grind)
    | exact resolve eq182 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq661
  have eq1769 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1915 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (τ X0) X0 (τ X0)
       have i₂ := eq1769 (τ X0)
       grind)
    | exact superpose eq1769 eq27
    | (have j1 := eq1769 (τ X0)
       grind)
    | exact resolve eq27 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1769
  have eq1949 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1915 X0
       have j1 := eq12 (k (σ (τ X0)) X0) (σ (τ X0))
       grind)
    | (have r₁ := eq1915 X0
       have r₂ := eq12 X0 (σ (τ X0))
       grind)
    | exact resolve eq1915 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq1961 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1949 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1949
    | exact resolve eq1949 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq1982 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1961 X0
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq1961
    | (have j1 := eq88 X0
       grind)
    | exact resolve eq1961 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1961
  have eq2017 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1982 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq1982 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1982 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq2159 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq2017 (σ X0)
       grind)
    | exact superpose eq2017 eq22
    | exact resolve eq22 eq2017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2017
  have eq2174 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2159 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2159
    | exact resolve eq2159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159
  have eq7273 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq387 X0 X1
       have j1 := eq380 X1 X0
       grind)
    | (have r₁ := eq387 X1 X0
       have r₂ := eq380 X0 X1
       grind)
    | (have r₁ := eq387 X1 X1
       have r₂ := eq380 X1 X1
       grind)
    | exact resolve eq387 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq387
  have eq7288 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7273 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7273
    | exact resolve eq7273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7312 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7273 y x
       grind)
    | exact superpose eq7273 eq16
    | (have j1 := eq7273 y x
       grind)
    | exact resolve eq16 eq7273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7273
  have eq7404 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7288 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq7288
    | (have j0 := eq7288 X0 X1
       grind)
    | exact resolve eq7288 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7288
  have eq7416 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7404 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7404
    | (have j0 := eq7404 X1 X1
       grind)
    | exact resolve eq7404 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7404
  have eq7507 : ∀ X0 : G, (M.op (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7416 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq2174 X0
       grind)
    | exact superpose eq2174 eq7416
    | (have j0 := eq7416 X0 X0
       grind)
    | exact resolve eq7416 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8171 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7312
       have i₂ := eq7416 x y
       grind)
    | exact superpose eq7416 eq7312
    | (have j1 := eq7416 x (σ y)
       grind)
    | exact resolve eq7312 eq7416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7312 eq7416
  have eq8176 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq8171
  have eq8181 : y = (M.op (τ (σ y)) y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7507 y
       have i₂ := eq8176
       grind)
    | exact superpose eq8176 eq7507
    | (have j0 := eq7507 y
       grind)
    | exact resolve eq7507 eq8176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7507
  have eq8182 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2174 y
       have i₂ := eq8176
       grind)
    | exact superpose eq8176 eq2174
    | exact resolve eq2174 eq8176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174 eq8176
  have eq8255 : y = (M.op (τ (σ y)) y) ∨ y = (M.op y y) := by grind
  clear eq8181
  have eq8283 : y = (k (τ (σ y)) y) := by
    first
    | (have j1 := eq12 (τ (σ y)) y
       grind)
    | (have r₁ := eq8182
       have r₂ := eq12 x y
       grind)
    | exact resolve eq8182 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8182
  have eq8284 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8255
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8255
    | exact resolve eq8255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8255
  have eq8285 : y = (M.op y y) := by grind
  clear eq8284
  have eq8288 : y = (k y y) := by
    first
    | (have i₁ := eq8283
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8283
    | exact resolve eq8283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8283
  have eq8293 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq679 y
       have i₂ := eq8288
       grind)
    | exact superpose eq8288 eq679
    | (have j0 := eq679 y
       grind)
    | exact resolve eq679 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq8288
  have eq8338 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq8293
  have eq8349 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq8285
       grind)
    | exact superpose eq8285 eq73
    | exact resolve eq73 eq8285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8407 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq585 y y x
       have i₂ := eq8285
       grind)
    | exact superpose eq8285 eq585
    | exact resolve eq585 eq8285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8285
  have eq8418 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq8407 X0
       have i₂ := eq91 y X0
       grind)
    | exact superpose eq91 eq8407
    | exact resolve eq8407 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq8407
  have eq8962 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 (σ y) X0
       have i₂ := eq8338
       grind)
    | exact superpose eq8338 eq73
    | exact resolve eq73 eq8338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq8338
  have eq9284 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8349 X0
       have i₂ := eq8418 X0
       grind)
    | exact superpose eq8418 eq8349
    | exact resolve eq8349 eq8418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8349
  have eq9285 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq8418 X0
       have i₂ := eq9284 X0
       grind)
    | exact superpose eq9284 eq8418
    | exact resolve eq8418 eq9284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8418
  have eq9350 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 y X1 X0
       have i₂ := eq9284 X0
       grind)
    | exact superpose eq9284 eq585
    | exact resolve eq585 eq9284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq9430 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9350 X0 X0
       have i₂ := eq9284 X0
       grind)
    | exact superpose eq9284 eq9350
    | exact resolve eq9350 eq9284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9284 eq9350
  have eq13376 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8962 X0
       have i₂ := eq9430 X0 (σ y)
       grind)
    | exact superpose eq9430 eq8962
    | exact resolve eq8962 eq9430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8962
  have eq13460 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9430 X0 (σ y)
       have i₂ := eq13376 X0
       grind)
    | exact superpose eq13376 eq9430
    | exact resolve eq9430 eq13376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9430 eq13376
  have eq13799 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13460 (σ x)
       grind)
    | exact superpose eq13460 eq16
    | exact resolve eq16 eq13460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13460
  have eq13812 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq13799
       have i₂ := eq9285 x
       grind)
    | exact superpose eq9285 eq13799
    | exact resolve eq13799 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9285 eq13799
  have eq13813 : False := by grind
  exact eq13813

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, y = (M.op (M.op y (M.op (M.op (M.op x y) (M.op x y)) X0)) y) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq550 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq16
    | exact resolve eq16 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq555 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq185 eq188
    | exact resolve eq188 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq558 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq555 eq16
    | exact resolve eq16 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq564 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq550 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq550
    | exact resolve eq550 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq574 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq558 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq558
    | exact resolve eq558 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq616 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : y = (k (M.op (M.op x y) (M.op x y)) y) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq180
       have i₂ := eq11 (M.op sF0 sF0) y
       grind)
    | exact superpose eq11 eq180
    | (have j1 := eq11 (M.op (M.op x y) (M.op x y)) y
       grind)
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq709 : y = (k (M.op (M.op x y) (M.op x y)) y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq12 (M.op (M.op x y) (M.op x y)) y
       grind)
    | (have r₁ := eq640
       have r₂ := eq12 (M.op (M.op x y) (M.op x y)) y
       grind)
    | (have r₁ := eq640
       have r₂ := eq12 y y
       grind)
    | exact resolve eq640 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq814 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq616
       grind)
    | exact superpose eq616 eq40
    | exact resolve eq40 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq815 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq814
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq814
    | exact resolve eq814 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq817 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq815
    | exact resolve eq815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq879 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq191
    | exact resolve eq191 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq894 : y = (M.op (M.op y (M.op x y)) y) := by
    first
    | (have i₁ := eq184 sF0
       have i₂ := eq879 sF0
       grind)
    | exact superpose eq879 eq184
    | exact resolve eq184 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq902 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq879 X0
       grind)
    | exact superpose eq879 eq16
    | exact resolve eq16 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq879 X0
       grind)
    | exact superpose eq879 eq16
    | exact resolve eq16 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1190 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq902
    | exact resolve eq902 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1194 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq902
    | exact resolve eq902 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq817 eq618
    | exact resolve eq618 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq817
  have eq2039 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2028
       have r₂ := eq27
       grind)
    | exact resolve eq2028 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq2061 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2039 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq2039
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2039
       grind)
    | exact resolve eq13 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2062 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq2061 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq2147 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2039
       have i₂ := eq2062 sF3
       grind)
    | exact superpose eq2062 eq2039
    | exact resolve eq2039 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039 eq2062
  have eq2158 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq2147
  have eq2187 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2158 eq152
    | exact resolve eq152 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2158
  have eq2203 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq2187
    | exact resolve eq2187 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187
  have eq2207 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq682 y
       grind)
    | (have r₁ := eq2203
       have r₂ := eq682 y
       grind)
    | exact resolve eq2203 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq2203
  have eq2226 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq903 y X0
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq903
    | exact resolve eq903 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2227 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq902 y X0
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq902
    | exact resolve eq902 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq2229 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2207
       grind)
    | exact resolve eq13 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2230 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq2233 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2226 X0
       have i₂ := eq564 X0
       grind)
    | exact superpose eq564 eq2226
    | exact resolve eq2226 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq2226
  have eq2303 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2207
       have i₂ := eq2230 y
       grind)
    | exact superpose eq2230 eq2207
    | exact resolve eq2207 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207 eq2230
  have eq2331 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2303
  have eq2357 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2331
       grind)
    | exact superpose eq2331 eq40
    | exact resolve eq40 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2371 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2357
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2357
    | exact resolve eq2357 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq2384 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2371 eq680
    | (have j0 := eq680 (σ y) (σ y)
       grind)
    | (have r₁ := eq680 (σ y) (σ y)
       have r₂ := eq2371
       grind)
    | exact resolve eq680 eq2371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2385 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2384
  have eq2386 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2385
  have eq2415 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2386 eq903
    | exact resolve eq903 eq2386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq2386
  have eq2424 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq574 eq2415
    | exact resolve eq2415 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq2415
  have eq3667 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2227 X0
       have i₂ := eq2233 X0
       grind)
    | exact superpose eq2233 eq2227
    | exact resolve eq2227 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq3700 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq3811 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2233 X0
       have i₂ := eq3700 X0
       grind)
    | exact superpose eq3700 eq2233
    | exact resolve eq2233 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq3827 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 y X0
       have i₂ := eq3700 X0
       grind)
    | exact superpose eq3700 eq16
    | exact resolve eq16 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3854 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811
  have eq3869 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f3869_14 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f3869_15 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f3869_24 : X1 ≠ (M.op (M.op X1 X0) X1) := by grind
    have f3869_25 : x ≠ (M.op x y) := by grind
    have f3869_26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f3869_27 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f3869_15 X0
         grind)
      | (have r₁ := f3869_15 X0
         have r₂ := f3869_25
         grind)
      | exact resolve f3869_15 f3869_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3869_28 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f3869_14 X0 X1
         grind)
      | (have r₁ := f3869_14 X0 X1
         have r₂ := f3869_25
         grind)
      | exact resolve f3869_14 f3869_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3869_29 : ∀ X0 : G, (M.op y X0) = X0 := by
      intro X0
      first
      | (have j0 := f3869_27 X0
         grind)
      | (have r₁ := f3869_27 X0
         have r₂ := f3869_26
         grind)
      | exact resolve f3869_27 f3869_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3869_30 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
      intro X0 X1
      first
      | (have j0 := f3869_28 X0 X1
         grind)
      | (have r₁ := f3869_28 X0 X1
         have r₂ := f3869_26
         grind)
      | exact resolve f3869_28 f3869_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3869_31 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f3869_30 X0 X1
         have i₂ := f3869_29 X1
         grind)
      | exact superpose f3869_29 f3869_30
      | exact resolve f3869_30 f3869_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3869_34 : X1 ≠ X1 := by
      first
      | (have i₁ := f3869_24
         have i₂ := f3869_31 X0 X1
         grind)
      | exact superpose f3869_31 f3869_24
      | (have r₁ := f3869_24
         have r₂ := f3869_31 X0 X1
         grind)
      | exact resolve f3869_24 f3869_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3869_35 : False := by grind
    exact f3869_35
  clear eq3700 eq3827
  have eq3984 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3854 x
       grind)
    | exact superpose eq3854 eq18
    | (have j1 := eq3854 x
       grind)
    | exact resolve eq18 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq4042 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3984 eq185
    | exact resolve eq185 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4060 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3984 eq1194
    | exact resolve eq1194 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4076 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4060 eq4042
    | exact resolve eq4042 eq4060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4042 eq4060
  have eq4080 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4076
    | exact resolve eq4076 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076
  have eq4081 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3984 eq4080
    | exact resolve eq4080 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4080
  have eq4352 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4081 eq31
    | exact resolve eq31 eq4081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4081
  have eq4459 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq4352
    | exact resolve eq4352 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4352
  have eq4466 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq4459
       grind)
    | exact superpose eq4459 eq24
    | exact resolve eq24 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4503 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2331
       have i₂ := eq4459
       grind)
    | exact superpose eq4459 eq2331
    | exact resolve eq2331 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331 eq4459
  have eq4545 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4503
  have eq4592 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3984 eq4545
    | exact resolve eq4545 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq4593 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4592
  have eq4611 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq4466
    | exact resolve eq4466 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4969 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4593 eq41
    | exact resolve eq41 eq4593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4593
  have eq4984 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4969
    | exact resolve eq4969 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4969
  have eq4997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4984 eq680
    | (have j0 := eq680 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq680 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq4984
       grind)
    | exact resolve eq680 eq4984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq4984
  have eq4998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4997
  have eq4999 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4998
  have eq5026 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4999 eq16
    | exact resolve eq16 eq4999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4999
  have eq5052 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3869 eq5026
    | exact resolve eq5026 eq3869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3869 eq5026
  have eq5084 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4611 eq5052
    | exact resolve eq5052 eq4611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052
  have eq5126 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq5084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5084
  have eq5140 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3984 eq5126
    | (have j0 := eq5126 X0
       grind)
    | exact resolve eq5126 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5126
  have eq5141 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5140
  have eq5171 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5141 eq2424
    | exact resolve eq2424 eq5141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424 eq5141
  have eq5218 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171
  have eq5483 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5218 eq26
    | (have j1 := eq5218 (σ x)
       grind)
    | exact resolve eq26 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218
  have eq5530 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5483 eq27
    | exact resolve eq27 eq5483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5483
  have eq5569 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4611 eq5530
    | (have r₁ := eq5530
       have r₂ := eq4611
       grind)
    | exact resolve eq5530 eq4611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq5570 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq5569
  have eq5571 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq5570
  have eq5572 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3984 eq5571
    | exact resolve eq5571 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984 eq5571
  have eq5573 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5572
  have eq5575 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5573 eq27
    | exact resolve eq27 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5578 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5573 eq185
    | exact resolve eq185 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq5596 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5573 eq1194
    | exact resolve eq1194 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq5613 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5596 eq5578
    | exact resolve eq5578 eq5596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5578
  have eq5617 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5613
    | exact resolve eq5613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5613
  have eq5618 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5573 eq5617
    | exact resolve eq5617 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573 eq5617
  have eq5619 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4611 eq5575
    | exact resolve eq5575 eq4611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq5620 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5619
  have eq5621 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq5620
       have r₂ := eq5618
       grind)
    | exact resolve eq5620 eq5618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5618 eq5620
  have eq5749 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq5621
       grind)
    | exact superpose eq5621 eq18
    | exact resolve eq18 eq5621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5760 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1190
       have i₂ := eq5621
       grind)
    | exact superpose eq5621 eq1190
    | exact resolve eq1190 eq5621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5824 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5596 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq5596
       grind)
    | exact resolve eq13 eq5596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5848 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5824 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5824
  have eq5907 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq5760 eq180
    | exact resolve eq180 eq5760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq5760
  have eq5935 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5749 eq5907
    | exact resolve eq5907 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5749 eq5907
  have eq6087 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq5935
  have eq6088 : x = y := by
    first
    | (have r₁ := eq6087
       have r₂ := eq5621
       grind)
    | exact resolve eq6087 eq5621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5621 eq6087
  have eq6095 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6088
       grind)
    | exact superpose eq6088 eq18
    | exact resolve eq18 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6096 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6088
       grind)
    | exact superpose eq6088 eq24
    | exact resolve eq24 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq6116 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq894
       have i₂ := eq6088
       grind)
    | exact superpose eq6088 eq894
    | exact resolve eq894 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq6158 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1190 eq6116
    | exact resolve eq6116 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq6116
  have eq6161 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6096
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6096
    | exact resolve eq6096 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6096
  have eq6163 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6161 eq26
    | exact resolve eq26 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6161
  have eq6272 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq6095
       grind)
    | exact superpose eq6095 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq6095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6095
  have eq6290 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq6272
  have eq6344 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6163 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163
  have eq6362 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6344
  have eq6642 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6290
       grind)
    | exact superpose eq6290 eq39
    | exact resolve eq39 eq6290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq6290
  have eq6653 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6642
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6642
    | exact resolve eq6642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6642
  have eq6655 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6653
    | exact resolve eq6653 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6653
  have eq7524 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5596
       have i₂ := eq5848 sF2
       grind)
    | exact superpose eq5848 eq5596
    | exact resolve eq5596 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596 eq5848
  have eq7559 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7524
  have eq7713 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7559 eq6655
    | exact resolve eq6655 eq7559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655 eq7559
  have eq7734 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq7713
  have eq7740 : x = (M.op x y) := by
    first
    | (have r₁ := eq7734
       have r₂ := eq5575
       grind)
    | exact resolve eq7734 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5575 eq7734
  have eq7749 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7740
       grind)
    | exact superpose eq7740 eq22
    | exact resolve eq22 eq7740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq7770 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6158
       have i₂ := eq7740
       grind)
    | exact superpose eq7740 eq6158
    | exact resolve eq6158 eq7740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6158
  have eq7789 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7749 eq20
    | exact resolve eq20 eq7749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7749
  have eq7915 : y = (k (M.op x y) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7770 eq709
    | exact resolve eq709 eq7770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq7919 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7770 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq7770
       grind)
    | exact resolve eq13 eq7770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7770
  have eq7941 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq7919 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7919
  have eq7947 : x = (k (M.op x y) x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7915
       have i₂ := eq6088
       grind)
    | exact superpose eq6088 eq7915
    | exact resolve eq7915 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915
  have eq7954 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7947
       have i₂ := eq7740
       grind)
    | exact superpose eq7740 eq7947
    | exact resolve eq7947 eq7740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7947
  have eq7957 : y = (k y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7954
       have i₂ := eq7941 y
       grind)
    | exact superpose eq7941 eq7954
    | exact resolve eq7954 eq7941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7941 eq7954
  have eq7958 : x = (k x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7957
       have i₂ := eq6088
       grind)
    | exact superpose eq6088 eq7957
    | exact resolve eq7957 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6088 eq7957
  have eq7959 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7958
       have i₂ := eq7740
       grind)
    | exact superpose eq7740 eq7958
    | exact resolve eq7958 eq7740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7740 eq7958
  have eq7960 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq7959
  have eq7965 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7960 eq37
    | exact resolve eq37 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7960
  have eq7982 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq7965
    | exact resolve eq7965 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7965
  have eq7984 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq7789 eq7982
    | exact resolve eq7982 eq7789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7982
  have eq7989 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7984 eq6362
    | exact resolve eq6362 eq7984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6362 eq7984
  have eq8008 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7989
  have eq8025 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8008 eq27
    | exact resolve eq27 eq8008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8008
  have eq8080 : False := by grind
  exact eq8080

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq183
  have eq550 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq16
    | exact resolve eq16 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq564 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq550 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq550
    | exact resolve eq550 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq580 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq580 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq580 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq580 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq632 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq646 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq659 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq659 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq676 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq581 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq581
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq581 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq581 y
       grind)
    | exact superpose eq581 eq40
    | exact resolve eq40 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq685 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq676 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq821 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq191
    | exact resolve eq191 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq191
  have eq829 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq821 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq821
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq821 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq821 X0
       grind)
    | exact superpose eq821 eq16
    | exact resolve eq16 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq821 X0
       grind)
    | exact superpose eq821 eq16
    | exact resolve eq16 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq871 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq838
    | exact resolve eq838 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1409 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0) X0
       have i₂ := eq840 X0
       grind)
    | exact superpose eq840 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq840 X0
       grind)
    | exact resolve eq11 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq1418 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1420 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1418 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1418 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1418 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1971 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq632
       grind)
    | exact superpose eq632 eq40
    | exact resolve eq40 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq632
  have eq1972 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1971
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1971
    | exact resolve eq1971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1974 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1972
    | exact resolve eq1972 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq15772 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq685 X0
       have i₂ := eq1420 X0
       grind)
    | exact superpose eq1420 eq685
    | (have j0 := eq685 X0
       have j1 := eq1420 X0
       grind)
    | exact resolve eq685 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq1420
  have eq15859 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15772 X0
       have j1 := eq660 X0
       grind)
    | (have r₁ := eq15772 X0
       have r₂ := eq660 X0
       grind)
    | exact resolve eq15772 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq15772
  have eq15896 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15859 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq15859 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq15859 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15859
  have eq15928 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq871 X0 X0
       have i₂ := eq15896 X0
       grind)
    | exact superpose eq15896 eq871
    | exact resolve eq871 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq15935 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq821 X0
       have i₂ := eq15896 X0
       grind)
    | exact superpose eq15896 eq821
    | exact resolve eq821 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq15936 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 X1
       have i₂ := eq15896 X0
       grind)
    | exact superpose eq15896 eq838
    | exact resolve eq838 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq15937 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (k X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq15896 X0
       grind)
    | exact superpose eq15896 eq839
    | exact resolve eq839 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq16051 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15935 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq15935
    | exact resolve eq15935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1974 eq646
    | exact resolve eq646 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq1974
  have eq22443 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq22432
       have r₂ := eq27
       grind)
    | exact resolve eq22432 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22432
  have eq22451 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22443
       have i₂ := eq15896 sF3
       grind)
    | exact superpose eq15896 eq22443
    | exact resolve eq22443 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22443
  have eq22457 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22451
       have i₂ := eq15896 sF3
       grind)
    | exact superpose eq15896 eq22451
    | exact resolve eq22451 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22451
  have eq22463 : x = (k y y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22457
       have i₂ := eq15896 y
       grind)
    | exact superpose eq15896 eq22457
    | exact resolve eq22457 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22457
  have eq22465 : (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq22463
       have i₂ := eq15896 y
       grind)
    | exact superpose eq15896 eq22463
    | exact resolve eq22463 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896 eq22463
  have eq22547 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq22465 eq152
    | exact resolve eq152 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq22465
  have eq22595 : y = (k y y) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq31 eq22547
    | exact resolve eq22547 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq22547
  have eq22596 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k y y) := by grind
  clear eq22595
  have eq22614 : (τ (σ x)) = (k y y) ∨ x = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq22596 eq115
    | exact resolve eq115 eq22596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq22596
  have eq22670 : x = (k y y) ∨ x = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq29 eq22614
    | exact resolve eq22614 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22614
  have eq22671 : y = (k y y) ∨ x = (k y y) := by grind
  clear eq22670
  have eq22708 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq15936 y X0
       have i₂ := eq22671
       grind)
    | exact superpose eq22671 eq15936
    | exact resolve eq15936 eq22671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22709 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq15937 y X0
       have i₂ := eq22671
       grind)
    | exact superpose eq22671 eq15937
    | exact resolve eq15937 eq22671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15937 eq22671
  have eq22733 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq22709 X0
       have i₂ := eq564 X0
       grind)
    | exact superpose eq564 eq22709
    | exact resolve eq22709 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq22709
  have eq23940 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (k y y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq22708 X0
       have i₂ := eq22733 X0
       grind)
    | exact superpose eq22733 eq22708
    | exact resolve eq22708 eq22733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22708
  have eq23989 : ∀ X0 : G, x = (k y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23940
  have eq24146 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15928 y
       have i₂ := eq23989 X0
       grind)
    | exact superpose eq23989 eq15928
    | (have j1 := eq23989 x
       grind)
    | exact resolve eq15928 eq23989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15928
  have eq24155 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16051 y
       have i₂ := eq23989 X0
       grind)
    | exact superpose eq23989 eq16051
    | (have j1 := eq23989 X0
       grind)
    | exact resolve eq16051 eq23989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16051 eq23989
  have eq24167 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24155 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24155
    | (have j0 := eq24155 X0
       grind)
    | exact resolve eq24155 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24155
  have eq24181 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24167 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24167
    | (have j0 := eq24167 X0
       grind)
    | exact resolve eq24167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24167
  have eq24187 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq24181
    | (have j0 := eq24181 X0
       grind)
    | exact resolve eq24181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24181
  have eq24333 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq680
       have i₂ := eq24187 y
       grind)
    | exact superpose eq24187 eq680
    | exact resolve eq680 eq24187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq24350 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 y X0
       have i₂ := eq24187 X0
       grind)
    | exact superpose eq24187 eq16
    | exact resolve eq16 eq24187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24404 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f24404_13 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f24404_14 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f24404_23 : X1 ≠ (M.op (M.op X1 X0) X1) := by grind
    have f24404_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f24404_27 : ∀ X0 : G, (M.op y X0) = X0 := by
      intro X0
      first
      | (have j0 := f24404_14 X0
         grind)
      | (have r₁ := f24404_14 X0
         have r₂ := f24404_24
         grind)
      | exact resolve f24404_14 f24404_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24404_28 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
      intro X0 X1
      first
      | (have j0 := f24404_13 X0 X1
         grind)
      | (have r₁ := f24404_13 X0 X1
         have r₂ := f24404_24
         grind)
      | exact resolve f24404_13 f24404_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24404_29 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f24404_28 X0 X1
         have i₂ := f24404_27 X1
         grind)
      | exact superpose f24404_27 f24404_28
      | exact resolve f24404_28 f24404_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24404_32 : X1 ≠ X1 := by
      first
      | (have i₁ := f24404_23
         have i₂ := f24404_29 X0 X1
         grind)
      | exact superpose f24404_29 f24404_23
      | (have r₁ := f24404_23
         have r₂ := f24404_29 X0 X1
         grind)
      | exact resolve f24404_23 f24404_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24404_33 : False := by grind
    exact f24404_33
  clear eq24187 eq24350
  have eq24413 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24333
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24333
    | exact resolve eq24333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24333
  have eq25246 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24413 eq15936
    | exact resolve eq15936 eq24413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15936 eq24413
  have eq25268 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24404 eq25246
    | exact resolve eq25246 eq24404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25246
  have eq26098 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq24146 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24146
  have eq26099 : x = (M.op y x) := by grind
  clear eq26098
  have eq26136 : y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq22733 x
       have i₂ := eq26099
       grind)
    | exact superpose eq26099 eq22733
    | exact resolve eq22733 eq26099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22733 eq26099
  have eq26166 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26136
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26136
    | exact resolve eq26136 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26136
  have eq26212 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15935 y
       have i₂ := eq26166
       grind)
    | exact superpose eq26166 eq15935
    | exact resolve eq15935 eq26166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15935 eq26166
  have eq26231 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26212
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26212
    | exact resolve eq26212 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq26212
  have eq26232 : y = (M.op x y) := by grind
  clear eq26231
  have eq26245 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq26232
       grind)
    | exact superpose eq26232 eq24
    | exact resolve eq24 eq26232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26232
  have eq26338 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26245 eq20
    | exact resolve eq20 eq26245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26245
  have eq30440 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25268 eq24404
    | exact resolve eq24404 eq25268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24404 eq25268
  have eq30535 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30440
  have eq30793 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30535 eq26
    | (have j1 := eq30535 (σ x)
       grind)
    | exact resolve eq26 eq30535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30535
  have eq30817 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq30793
  have eq30826 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq30817 eq27
    | exact resolve eq27 eq30817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30817
  have eq30870 : False := by grind
  exact eq30870

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq77 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq93 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq78 (σ X0)
       grind)
    | exact superpose eq78 eq15
    | exact resolve eq15 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq78 (τ X0)
       grind)
    | exact superpose eq78 eq32
    | exact resolve eq32 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq95
    | exact resolve eq95 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq93
    | exact resolve eq93 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq93
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq214 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq104 X1
       grind)
    | exact superpose eq104 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq4198 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X1 (τ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq214
    | (have j0 := eq214 X1 (τ X0)
       grind)
    | exact resolve eq214 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq214
  have eq4296 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4198 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4198
    | (have j0 := eq4198 X0 X1
       grind)
    | exact resolve eq4198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198
  have eq4300 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4296 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4296
    | (have j0 := eq4296 X0 X1
       grind)
    | exact resolve eq4296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4302 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4300 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4300
    | (have j0 := eq4300 X0 X1
       grind)
    | exact resolve eq4300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4300
  have eq4303 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4302 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq4302
    | (have j0 := eq4302 X0 X1
       grind)
    | exact resolve eq4302 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4302
  have eq4304 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq4303 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq4303 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq4303 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq4305 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4304 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4304
    | (have j0 := eq4304 X0 X1
       grind)
    | exact resolve eq4304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4304
  have eq4306 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4305 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4305
    | exact resolve eq4305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4313 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4305 (σ X1) X0
       grind)
    | exact superpose eq4305 eq15
    | (have j1 := eq4305 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq4305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4305
  have eq4347 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4306 X0 (τ X1)
       grind)
    | exact superpose eq4306 eq19
    | (have j1 := eq4306 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq4306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4306
  have eq4661 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4347 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4347
    | exact resolve eq4347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4347
  have eq4835 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4661 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4661
    | (have j0 := eq4661 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq4661 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4661
  have eq5390 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4313 x y
       grind)
    | exact superpose eq4313 eq16
    | (have j1 := eq4313 x y
       grind)
    | exact resolve eq16 eq4313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4313
  have eq5450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5390
       have i₂ := eq4835 y x
       grind)
    | exact superpose eq4835 eq5390
    | (have j1 := eq4835 (σ x) (σ y)
       grind)
    | (have r₁ := eq5390
       have r₂ := eq4835 y x
       grind)
    | (have r₁ := eq5390
       have r₂ := eq4835 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5390
       have r₂ := eq4835 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5390 eq4835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835 eq5390
  have eq5451 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5450
  have eq5454 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5451
       grind)
    | exact superpose eq5451 eq16
    | exact resolve eq16 eq5451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5451
  have eq5455 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5454
       have r₂ := eq104 x
       grind)
    | exact resolve eq5454 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5454
  have eq5456 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5455
       grind)
    | exact superpose eq5455 eq16
    | exact resolve eq16 eq5455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5457 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5455
       grind)
    | exact superpose eq5455 eq10
    | exact resolve eq10 eq5455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5455
  have eq5522 : x = y := by
    first
    | (have i₁ := eq5457
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5457
    | exact resolve eq5457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5457
  have eq5523 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5456
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq5456
    | exact resolve eq5456 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq5456
  have eq5524 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5523
       have i₂ := eq5522
       grind)
    | exact superpose eq5522 eq5523
    | exact resolve eq5523 eq5522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522 eq5523
  have eq5525 : False := by grind
  exact eq5525

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ x = (k y x) := by
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
  have eq72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq37
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq122 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq119
  have eq123 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq122
  have eq162 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq213 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq699 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq706 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq699 X0
       grind)
    | exact superpose eq699 eq14
    | exact resolve eq14 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq1046 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq706
    | exact resolve eq706 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1048 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq57 eq706
    | exact resolve eq706 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq706
  have eq9110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9110
    | exact resolve eq9110 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9110
  have eq9122 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq9111
       have r₂ := eq28
       grind)
    | exact resolve eq9111 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9111
  have eq9126 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq9122
    | exact resolve eq9122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9122
  have eq9131 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9126 eq72
    | (have r₁ := eq72
       have r₂ := eq9126
       grind)
    | exact resolve eq72 eq9126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq9126
  have eq9183 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq9131
  have eq9184 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq9183
  have eq9208 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9184 eq101
    | exact resolve eq101 eq9184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq9209 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9184 eq104
    | exact resolve eq104 eq9184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq9184
  have eq9218 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9209
  have eq9228 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq9208
    | exact resolve eq9208 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9208
  have eq9235 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9228
       have r₂ := eq71
       grind)
    | exact resolve eq9228 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq9228
  have eq9238 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq9235
       grind)
    | exact superpose eq9235 eq89
    | exact resolve eq89 eq9235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq9235
  have eq9255 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9238
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9238
    | exact resolve eq9238 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9238
  have eq9273 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9255 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9255
  have eq9274 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9273
  have eq9278 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq9274
    | exact resolve eq9274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9274
  have eq9289 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq9278
    | exact resolve eq9278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9278
  have eq9293 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq9218
       grind)
    | exact superpose eq9218 eq52
    | exact resolve eq52 eq9218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9218
  have eq9363 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq9293
    | exact resolve eq9293 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9293
  have eq10283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9289 eq9363
    | exact resolve eq9363 eq9289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9289
  have eq10329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10283
  have eq10336 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq10329
       have r₂ := eq28
       grind)
    | exact resolve eq10329 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10329
  have eq10362 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10336 eq1048
    | exact resolve eq1048 eq10336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq10336
  have eq10738 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10362 eq9363
    | exact resolve eq9363 eq10362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9363 eq10362
  have eq10786 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq10738
  have eq10835 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10786 eq30
    | exact resolve eq30 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10786
  have eq10958 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq10835
    | exact resolve eq10835 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10835
  have eq10959 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq10958
  have eq10980 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq10959 eq29
    | exact resolve eq29 eq10959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq11125 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq10980
    | exact resolve eq10980 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10980
  have eq11214 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11125 eq1046
    | exact resolve eq1046 eq11125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq11567 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq11214
       grind)
    | exact superpose eq11214 eq52
    | exact resolve eq52 eq11214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11214
  have eq11662 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11567
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11567
    | exact resolve eq11567 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11567
  have eq12197 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10959 eq11662
    | exact resolve eq11662 eq10959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10959 eq11662
  have eq12275 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq12197
  have eq12601 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12275 eq162
    | exact resolve eq162 eq12275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq12275
  have eq12671 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq12601
    | exact resolve eq12601 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12601
  have eq13010 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq12671 eq213
    | exact resolve eq213 eq12671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq12671
  have eq13686 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq11125 eq13010
    | exact resolve eq13010 eq11125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13010
  have eq13720 : y = (M.op x y) ∨ x = y := by grind
  clear eq13686
  have eq13721 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13720
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13720
    | exact resolve eq13720 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13720
  have eq13801 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13721 eq11125
    | exact resolve eq11125 eq13721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11125 eq13721
  have eq13810 : x = y := by grind
  clear eq13801
  have eq13881 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13810
       grind)
    | exact superpose eq13810 eq19
    | exact resolve eq19 eq13810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq13882 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13810
       grind)
    | exact superpose eq13810 eq25
    | exact resolve eq25 eq13810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13810
  have eq14002 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13882
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13882
    | exact resolve eq13882 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13882
  have eq14344 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14002 eq27
    | exact resolve eq27 eq14002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14002
  have eq14655 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14344 eq70
    | exact resolve eq70 eq14344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq14344
  have eq14742 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14655
       have i₂ := eq13881
       grind)
    | exact superpose eq13881 eq14655
    | exact resolve eq14655 eq13881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13881 eq14655
  have eq14753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14742 eq15
    | exact resolve eq15 eq14742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14742
  have eq14800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14753
    | exact resolve eq14753 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14753
  have eq14809 : False := by grind
  exact eq14809
