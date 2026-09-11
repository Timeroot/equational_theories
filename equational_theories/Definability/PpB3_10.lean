import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2460`: `x = (x ◇ ((y ◇ x) ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2460 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2460 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2460.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq60 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k X1 (σ X0))
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq98 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq275 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
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
  have eq279 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq985 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq1027 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq985
    | (have j0 := eq985 X0 X1
       grind)
    | exact resolve eq985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq275
       have i₂ := eq1027 y x
       grind)
    | exact superpose eq1027 eq275
    | (have j1 := eq1027 y x
       grind)
    | (have r₁ := eq275
       have r₂ := eq1027 y x
       grind)
    | (have r₁ := eq275
       have r₂ := eq1027 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq275
       have r₂ := eq1027 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq275 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq1027
  have eq1692 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1691
  have eq1934 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq279 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq279
    | (have j0 := eq279 (τ X1) (τ X0)
       grind)
    | exact resolve eq279 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1966 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1934 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1934
    | (have j0 := eq1934 X0 X1
       grind)
    | exact resolve eq1934 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq1988 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1966 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1966
    | (have j0 := eq1966 X0 X1
       grind)
    | exact resolve eq1966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq2007 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1988 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1988
    | (have j0 := eq1988 X0 X1
       grind)
    | exact resolve eq1988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq2022 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2007 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2007
    | (have j0 := eq2007 X0 X1
       grind)
    | exact resolve eq2007 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2032 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2022 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq2022
    | (have j0 := eq2022 X0 X1
       grind)
    | exact resolve eq2022 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2022
  have eq2042 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2032 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2032
    | (have j0 := eq2032 X0 X1
       grind)
    | exact resolve eq2032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2047 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2042 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2042
    | (have j0 := eq2042 X0 X1
       grind)
    | exact resolve eq2042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq16076 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1692
       grind)
    | exact superpose eq1692 eq16
    | exact resolve eq16 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq16077 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16076
       have r₂ := eq22 x
       grind)
    | exact resolve eq16076 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16076
  have eq16265 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16077
       grind)
    | exact superpose eq16077 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16077
       grind)
    | exact resolve eq13 eq16077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16077
  have eq16267 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16265
  have eq18621 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16267
       grind)
    | exact superpose eq16267 eq16
    | exact resolve eq16 eq16267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16267
  have eq18622 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq18621
       have r₂ := eq22 x
       grind)
    | exact resolve eq18621 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18621
  have eq18851 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq60 x (σ y)
       have i₂ := eq18622
       grind)
    | exact superpose eq18622 eq60
    | (have j0 := eq60 x (σ y)
       grind)
    | (have r₁ := eq60 x (σ y)
       have r₂ := eq18622
       grind)
    | exact resolve eq60 eq18622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18622
  have eq18868 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by grind
  clear eq18851
  have eq18869 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by grind
  clear eq18868
  have eq18872 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18869
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18869
    | exact resolve eq18869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18869
  have eq19080 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq279 x y
       have i₂ := eq18872
       grind)
    | exact superpose eq18872 eq279
    | (have j0 := eq279 x y
       grind)
    | (have r₁ := eq279 x y
       have r₂ := eq18872
       grind)
    | exact resolve eq279 eq18872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18872
  have eq19107 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq19080
  have eq19108 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq19107
  have eq19114 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq279 x y
       grind)
    | (have r₁ := eq19108
       have r₂ := eq279 x y
       grind)
    | exact resolve eq19108 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq19108
  have eq19119 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19114
       grind)
    | exact superpose eq19114 eq16
    | exact resolve eq16 eq19114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19120 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq60 x (σ y)
       have i₂ := eq19114
       grind)
    | exact superpose eq19114 eq60
    | (have j0 := eq60 x (σ y)
       grind)
    | (have r₁ := eq60 x (σ y)
       have r₂ := eq19114
       grind)
    | exact resolve eq60 eq19114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq19114
  have eq19137 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19120
  have eq19138 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19137
  have eq19141 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19138
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19138
    | exact resolve eq19138 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19138
  have eq19468 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19141
       grind)
    | exact superpose eq19141 eq10
    | exact resolve eq10 eq19141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19141
  have eq19645 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19468
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19468
    | exact resolve eq19468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19468
  have eq19863 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19645
       grind)
    | exact superpose eq19645 eq16
    | exact resolve eq16 eq19645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19645
  have eq19864 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq19863
       have r₂ := eq22 x
       grind)
    | exact resolve eq19863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19863
  have eq19879 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq19864
       grind)
    | exact superpose eq19864 eq10
    | exact resolve eq10 eq19864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19864
  have eq20057 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq19879
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq19879
    | exact resolve eq19879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19879
  have eq20218 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2047 y x
       have i₂ := eq20057
       grind)
    | exact superpose eq20057 eq2047
    | (have j0 := eq2047 y x
       grind)
    | (have r₁ := eq2047 y x
       have r₂ := eq20057
       grind)
    | exact resolve eq2047 eq20057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047 eq20057
  have eq20238 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq20218
  have eq20242 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19119
       have i₂ := eq20238
       grind)
    | exact superpose eq20238 eq19119
    | exact resolve eq19119 eq20238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19119 eq20238
  have eq20252 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq20242
  have eq20646 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20252
       grind)
    | exact superpose eq20252 eq16
    | exact resolve eq16 eq20252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20252
  have eq20649 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq20646
       have r₂ := eq22 x
       grind)
    | exact resolve eq20646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20646
  have eq20650 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20649
       grind)
    | exact superpose eq20649 eq16
    | exact resolve eq16 eq20649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20651 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20649
       grind)
    | exact superpose eq20649 eq10
    | exact resolve eq10 eq20649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20649
  have eq20829 : x = y := by
    first
    | (have i₁ := eq20651
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20651
    | exact resolve eq20651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20651
  have eq20830 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20650
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20650
    | exact resolve eq20650 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20650
  have eq20831 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20830
       have i₂ := eq20829
       grind)
    | exact superpose eq20829 eq20830
    | exact resolve eq20830 eq20829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20829 eq20830
  have eq20832 : False := by grind
  exact eq20832

/-- `Equation2473`: `x = (x ◇ ((y ◇ y) ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyy_pyx_Equation2473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X0 X0) X1) X0
       have i₂ := eq16 (M.op (M.op X0 X0) X1) X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) X3)) X1 X2
       have i₂ := eq16 X0 (M.op (M.op X1 X1) X2) X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op X0 (M.op (M.op X1 X1) X2))) = (M.op X1 (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 (M.op (M.op X1 X1) X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op (M.op X1 X1) X2))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op (M.op X0 X0) X2))
       have r₂ := eq16 X0 X0 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) = X1 ∨ (k X1 (M.op X0 (M.op (M.op X1 X1) X2))) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 (M.op X0 (M.op (M.op X1 X1) X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 X1 (M.op X0 (M.op (M.op X1 X1) X2))
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (k X0 X0) X2)) X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1053 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (k X0 X0) X2)) X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1043 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1064 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1041
       grind)
    | exact superpose eq1041 eq39
    | exact resolve eq39 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1064
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1064
    | exact resolve eq1064 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1067 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1065
    | exact resolve eq1065 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1067 eq1042
    | exact resolve eq1042 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1082 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1075
       have r₂ := eq27
       grind)
    | exact resolve eq1075 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1087 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = X0 ∨ (σ y) = (k X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1082 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1082
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1082
       grind)
    | exact resolve eq12 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq1087 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1287 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1286
    | exact resolve eq1286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1288 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1287
  have eq1295 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1288 eq141
    | exact resolve eq141 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1288
  have eq1300 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1295
    | exact resolve eq1295 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1303 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1041 eq1300
    | exact resolve eq1300 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq1300
  have eq1304 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1303
  have eq1309 : ∀ X0 : G, y ≠ X0 ∨ (M.op x X0) = X0 ∨ y = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1304
       grind)
    | exact superpose eq1304 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1304
       grind)
    | exact resolve eq12 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1310 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x X1
       have i₂ := eq1304
       grind)
    | exact superpose eq1304 eq16
    | exact resolve eq16 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op (M.op X1 X1) X2)) X1 X2
       have i₂ := eq174 X1 X2 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op y X1) (M.op y X1)) X2)) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1310 (M.op X0 (M.op (M.op (M.op y X1) (M.op y X1)) X2)) X1
       have i₂ := eq16 X0 (M.op y X1) X2
       grind)
    | exact superpose eq16 eq1310
    | exact resolve eq1310 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1391 X0 X1 x
       have i₂ := eq1357 X0 (M.op y X1) x
       grind)
    | exact superpose eq1357 eq1391
    | exact resolve eq1391 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq1405 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1310 X0 x
       have i₂ := eq1399 X0 x
       grind)
    | exact superpose eq1399 eq1310
    | exact resolve eq1310 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310 eq1399
  have eq1430 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1439 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1430 x
       have i₂ := eq1304
       grind)
    | exact superpose eq1304 eq1430
    | exact resolve eq1430 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq1430
  have eq1445 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1439
  have eq1452 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1445
       grind)
    | exact superpose eq1445 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1445
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1445
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1445
       grind)
    | exact resolve eq13 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1453 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1452
  have eq1456 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1453
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1453
    | exact resolve eq1453 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq1460 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1456
       grind)
    | exact superpose eq1456 eq40
    | exact resolve eq40 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1456
  have eq1464 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1460
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1460
    | exact resolve eq1460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1466 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1464
    | exact resolve eq1464 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq1622 : y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq1309 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1623 : y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1622
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1622
    | exact resolve eq1622 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq1624 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1623
  have eq1628 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1624
       grind)
    | exact superpose eq1624 eq39
    | exact resolve eq39 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq1633 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1628
    | exact resolve eq1628 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1639 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1633 eq1042
    | exact resolve eq1042 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq1633
  have eq1645 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1639
  have eq1660 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) X1)) (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1645 eq16
    | exact resolve eq16 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1675 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op (σ y) X1) (M.op (σ y) X1)) X2)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1660 (M.op X0 (M.op (M.op (M.op sF3 X1) (M.op sF3 X1)) X2)) X1
       have i₂ := eq16 X0 (M.op sF3 X1) X2
       grind)
    | exact superpose eq16 eq1660
    | exact resolve eq1660 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1696 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1675 X0 X1 x
       have i₂ := eq1357 X0 (M.op sF3 X1) x
       grind)
    | exact superpose eq1357 eq1675
    | exact resolve eq1675 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq1707 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1696 eq1660
    | exact resolve eq1660 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660 eq1696
  have eq1758 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1772 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1645 eq1758
    | exact resolve eq1758 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645 eq1758
  have eq1784 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1772
  have eq1799 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1784 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1784
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1784
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1784
       grind)
    | exact resolve eq13 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784
  have eq1800 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1799
  have eq1811 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1800
    | exact resolve eq1800 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1466 eq1811
    | exact resolve eq1811 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq1811
  have eq1813 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1812
       have r₂ := eq27
       grind)
    | exact resolve eq1812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq2552 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) X3)) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq174 (M.op (M.op X1 X1) X2) X3 X0
       have i₂ := eq175 (M.op X0 (M.op (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) X3)) X1 X2 X3
       grind)
    | exact superpose eq175 eq174
    | exact resolve eq174 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2586 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2552 X0 X1 x x
       have i₂ := eq175 X0 X1 x x
       grind)
    | exact superpose eq175 eq2552
    | exact resolve eq2552 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2552
  have eq2626 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X0 X0) X1))) = (M.op X0 (M.op X0 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2627 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2626 x x
       have i₂ := eq1357 x x x
       grind)
    | exact superpose eq1357 eq2626
    | exact resolve eq2626 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626
  have eq5957 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2586 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2586
    | (have j0 := eq2586 x y
       grind)
    | exact resolve eq2586 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5967 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq2586
    | (have j0 := eq2586 (σ x) (σ y)
       grind)
    | exact resolve eq2586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6946 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1357 (M.op X0 X0) X0 (M.op X0 X0)
       have i₂ := eq2627 (M.op X0 X0)
       grind)
    | exact superpose eq2627 eq1357
    | exact resolve eq1357 eq2627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6947 : ∀ X0 : G, (M.op (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = (k X0 (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1040 (M.op x x) x (M.op x x)
       have i₂ := eq2627 (M.op x x)
       grind)
    | exact superpose eq2627 eq1040
    | (have j0 := eq1040 (M.op (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) X0 x
       grind)
    | exact resolve eq1040 eq2627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq6949 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 X0) X0 (M.op X0 X0)
       have i₂ := eq2627 (M.op X0 X0)
       grind)
    | exact superpose eq2627 eq16
    | exact resolve eq16 eq2627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6975 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1357 X1 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq2627 (M.op X0 X0)
       grind)
    | exact superpose eq2627 eq1357
    | exact resolve eq1357 eq2627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq7053 : ∀ X0 : G, (M.op (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0) = X0 ∨ (M.op X0 X0) = (k X0 (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6947 X0
       have i₂ := eq6975 X0 (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq6975 eq6947
    | (have j0 := eq6947 X0
       grind)
    | exact resolve eq6947 eq6975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6947 eq6975
  have eq7054 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq6946 X0
       have i₂ := eq2586 X0 X0
       grind)
    | exact superpose eq2586 eq6946
    | exact resolve eq6946 eq2586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6946
  have eq7069 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7053 X0
       have i₂ := eq6949 X0
       grind)
    | exact superpose eq6949 eq7053
    | (have j0 := eq7053 X0
       grind)
    | exact resolve eq7053 eq6949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6949 eq7053
  have eq7070 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq7069 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7069
  have eq7078 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7070 X0
       have i₂ := eq7054 X0
       grind)
    | exact superpose eq7054 eq7070
    | (have j0 := eq7070 X0
       grind)
    | exact resolve eq7070 eq7054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7054 eq7070
  have eq7081 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7078 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq7078 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq7078 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7078
  have eq11359 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1813 eq5967
    | exact resolve eq5967 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq11375 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11359
       have i₂ := eq7081 sF3
       grind)
    | exact superpose eq7081 eq11359
    | exact resolve eq11359 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11359
  have eq11379 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11375 eq115
    | exact resolve eq115 eq11375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq11386 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11375 eq1053
    | (have j0 := eq1053 (σ y) X1 x
       grind)
    | exact resolve eq1053 eq11375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11397 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11386 X0 X1
       have i₂ := eq7081 sF3
       grind)
    | exact superpose eq7081 eq11386
    | (have j0 := eq11386 X0 X1
       grind)
    | exact resolve eq11386 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11386
  have eq11401 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq11379
    | exact resolve eq11379 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11379
  have eq11404 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11375 eq11397
    | (have j0 := eq11397 X0 X1
       grind)
    | exact resolve eq11397 eq11375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11397
  have eq11416 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) y) = X0 ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1053 y X0 X1
       have i₂ := eq11401
       grind)
    | exact superpose eq11401 eq1053
    | (have j0 := eq1053 y X1 x
       grind)
    | exact resolve eq1053 eq11401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11429 : ∀ X0 X1 : G, y = (k y y) ∨ (M.op (M.op X0 (M.op x X1)) y) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11416 X0 X1
       have i₂ := eq7081 y
       grind)
    | exact superpose eq7081 eq11416
    | (have j0 := eq11416 X0 X1
       grind)
    | exact resolve eq11416 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11416
  have eq11435 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) y) = X0 ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11401 eq11429
    | (have j0 := eq11429 X0 X1
       grind)
    | exact resolve eq11429 eq11401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11401 eq11429
  have eq11504 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11404 eq2586
    | exact resolve eq2586 eq11404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11404
  have eq11630 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2586 (M.op X0 (M.op x X1)) y
       have i₂ := eq11435 X0 X1
       grind)
    | exact superpose eq11435 eq2586
    | exact resolve eq2586 eq11435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11435
  have eq12143 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11504 eq2627
    | exact resolve eq2627 eq11504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11504
  have eq12382 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12143
       have i₂ := eq7081 sF2
       grind)
    | exact superpose eq7081 eq12143
    | exact resolve eq12143 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12143
  have eq12406 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12382
    | exact resolve eq12382 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12382
  have eq12414 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1813 eq12406
    | exact resolve eq12406 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12406
  have eq12429 : (τ (σ y)) = (k x (τ (k (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12414 eq90
    | exact resolve eq90 eq12414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq12414
  have eq12438 : (τ (σ y)) = (k x (k x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq12429
    | exact resolve eq12429 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq12429
  have eq12439 : y = (k x (k x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq12438
    | exact resolve eq12438 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12438
  have eq12542 : (M.op x y) = (k x (M.op x x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2627 x
       have i₂ := eq11630 x x
       grind)
    | exact superpose eq11630 eq2627
    | exact resolve eq2627 eq11630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11630
  have eq12737 : (M.op x y) = (k x (k x x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12542
       have i₂ := eq7081 x
       grind)
    | exact superpose eq7081 eq12542
    | exact resolve eq12542 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12542
  have eq12757 : (M.op x y) = (k x (k x x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12737
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12737
    | exact resolve eq12737 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12737
  have eq12792 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12439
       have i₂ := eq12757
       grind)
    | exact superpose eq12757 eq12439
    | exact resolve eq12439 eq12757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12439 eq12757
  have eq12804 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq12792
  have eq12817 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12804 eq31
    | exact resolve eq31 eq12804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12804
  have eq13077 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12817
    | exact resolve eq12817 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12817
  have eq13078 : y = (M.op x y) ∨ x = y := by grind
  clear eq13077
  have eq13119 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq13078
       grind)
    | exact superpose eq13078 eq18
    | exact resolve eq18 eq13078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13120 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq13078
       grind)
    | exact superpose eq13078 eq24
    | exact resolve eq24 eq13078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13124 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq5957
       have i₂ := eq13078
       grind)
    | exact superpose eq13078 eq5957
    | exact resolve eq5957 eq13078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5957
  have eq13125 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq13078
  have eq13127 : x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq13124
       have i₂ := eq7081 sF0
       grind)
    | exact superpose eq7081 eq13124
    | exact resolve eq13124 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124
  have eq13130 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq13120
    | exact resolve eq13120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13120
  have eq13207 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq13127 eq41
    | exact resolve eq41 eq13127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq13209 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) (M.op x y)) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq13127 eq1053
    | (have j0 := eq1053 (M.op x y) X1 x
       grind)
    | exact resolve eq1053 eq13127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13214 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op X0 (M.op x X1)) (M.op x y)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq13209 X0 X1
       have i₂ := eq7081 sF0
       grind)
    | exact superpose eq7081 eq13209
    | (have j0 := eq13209 X0 X1
       grind)
    | exact resolve eq13209 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13209
  have eq13216 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq13207
    | exact resolve eq13207 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13207
  have eq13218 : ∀ X0 X1 : G, x = (M.op x y) ∨ (M.op (M.op X0 (M.op x X1)) (M.op x y)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq13127 eq13214
    | (have j0 := eq13214 X0 X1
       grind)
    | exact resolve eq13214 eq13127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13127 eq13214
  have eq13220 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq13216
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13216
    | exact resolve eq13216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13216
  have eq13222 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) (M.op x y)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq13218 X0 X1
       grind)
    | (have r₁ := eq13218 X0 X1
       have r₂ := eq13125
       grind)
    | exact resolve eq13218 eq13125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13218
  have eq13224 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq13130 eq13220
    | exact resolve eq13220 eq13130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13220
  have eq13226 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11375 eq13224
    | exact resolve eq13224 eq11375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11375 eq13224
  have eq13236 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13226 eq1053
    | (have j0 := eq1053 (σ y) X1 x
       grind)
    | exact resolve eq1053 eq13226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq13247 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq13236 X0 X1
       have i₂ := eq7081 sF3
       grind)
    | exact superpose eq7081 eq13236
    | (have j0 := eq13236 X0 X1
       grind)
    | exact resolve eq13236 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13254 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13226 eq13247
    | (have j0 := eq13247 X0 X1
       grind)
    | exact resolve eq13247 eq13226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13226 eq13247
  have eq13493 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq13222 eq2586
    | exact resolve eq2586 eq13222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13222
  have eq13564 : (k x (M.op x x)) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq2627 x
       have i₂ := eq13493 x x
       grind)
    | exact superpose eq13493 eq2627
    | exact resolve eq2627 eq13493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13493
  have eq13681 : (k x (k x x)) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq13564
       have i₂ := eq7081 x
       grind)
    | exact superpose eq7081 eq13564
    | exact resolve eq13564 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13564
  have eq13697 : (M.op x y) = (k x (k x x)) ∨ x = y := by
    first
    | exact superpose eq13119 eq13681
    | exact resolve eq13681 eq13119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13119 eq13681
  have eq13723 : (σ (M.op x y)) = (k (σ x) (σ (k x x))) ∨ x = y := by
    first
    | (have i₁ := eq35 (k x x)
       have i₂ := eq13697
       grind)
    | exact superpose eq13697 eq35
    | exact resolve eq35 eq13697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq13697
  have eq13732 : (σ (M.op x y)) = (k (σ x) (k (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq13723
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq13723
    | exact resolve eq13723 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723
  have eq13733 : (σ (M.op x y)) = (k (σ x) (k (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq13732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13732
    | exact resolve eq13732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13732
  have eq13734 : (σ (M.op x y)) = (k (σ x) (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq20 eq13733
    | exact resolve eq13733 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13733
  have eq13735 : (σ y) = (k (σ x) (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq13130 eq13734
    | exact resolve eq13734 eq13130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13734
  have eq15701 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13254 eq2586
    | exact resolve eq2586 eq13254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586 eq13254
  have eq16271 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15701 eq2627
    | exact resolve eq2627 eq15701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627 eq15701
  have eq16457 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16271
       have i₂ := eq7081 sF2
       grind)
    | exact superpose eq7081 eq16271
    | exact resolve eq16271 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16271
  have eq16487 : (M.op (σ x) (σ y)) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16457
    | exact resolve eq16457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16457
  have eq16522 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16487 eq13735
    | exact resolve eq13735 eq16487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13735 eq16487
  have eq16538 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16522
       have r₂ := eq13125
       grind)
    | exact resolve eq16522 eq13125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16522
  have eq16543 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1813 eq16538
    | exact resolve eq16538 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq16538
  have eq16545 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16543 eq27
    | exact resolve eq27 eq16543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16543
  have eq16643 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13130 eq16545
    | (have r₁ := eq16545
       have r₂ := eq13130
       grind)
    | exact resolve eq16545 eq13130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13130 eq16545
  have eq16644 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16643
  have eq16645 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16644
       have r₂ := eq13125
       grind)
    | exact resolve eq16644 eq13125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13125 eq16644
  have eq16647 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16645 eq31
    | exact resolve eq31 eq16645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq16645
  have eq16788 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16647
    | exact resolve eq16647 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16647
  have eq16789 : x = y := by grind
  clear eq16788
  have eq16814 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16789
       grind)
    | exact superpose eq16789 eq18
    | exact resolve eq18 eq16789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq16815 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16789
       grind)
    | exact superpose eq16789 eq24
    | exact resolve eq24 eq16789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16789
  have eq16905 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16815
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16815
    | exact resolve eq16815 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16815
  have eq16906 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq16814
       have i₂ := eq7081 x
       grind)
    | exact superpose eq7081 eq16814
    | exact resolve eq16814 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16814
  have eq16923 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16905 eq26
    | exact resolve eq26 eq16905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq16905
  have eq17131 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16923
       have i₂ := eq7081 sF2
       grind)
    | exact superpose eq7081 eq16923
    | exact resolve eq16923 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7081 eq16923
  have eq17829 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq16906
       grind)
    | exact superpose eq16906 eq39
    | exact resolve eq39 eq16906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16906
  have eq17851 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17829
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17829
    | exact resolve eq17829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17829
  have eq17858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17131 eq17851
    | exact resolve eq17851 eq17131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17131 eq17851
  have eq17864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17858
    | exact resolve eq17858 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq17858
  have eq17867 : False := by grind
  exact eq17867

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq174 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq178 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq179 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq181 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq179
    | (have j0 := eq179 X0 X1
       grind)
    | exact resolve eq179 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq185 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       have j1 := eq177 X0 X1
       grind)
    | (have r₁ := eq181 X0 X1
       have r₂ := eq177 X0 X1
       grind)
    | (have r₁ := eq181 X0 (k X1 X0)
       have r₂ := eq177 X0 X1
       grind)
    | (have r₁ := eq181 X0 X0
       have r₂ := eq177 X0 X0
       grind)
    | exact resolve eq181 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq181
  have eq517 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq185 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq185
    | exact resolve eq185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq185 x y
       grind)
    | exact superpose eq185 eq16
    | (have j1 := eq185 x y
       grind)
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq545 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq517
  have eq546 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq545
    | exact resolve eq545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq605 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq546 (τ X1) X0
       grind)
    | exact superpose eq546 eq18
    | (have j1 := eq546 (τ X1) X0
       grind)
    | exact resolve eq18 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq546
  have eq806 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq605
    | exact resolve eq605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq857 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq806
    | (have j0 := eq806 X0 X1
       grind)
    | exact resolve eq806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq953 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq531
       have i₂ := eq857 y x
       grind)
    | exact superpose eq857 eq531
    | (have j1 := eq857 (σ y) (σ x)
       grind)
    | (have r₁ := eq531
       have r₂ := eq857 y x
       grind)
    | exact resolve eq531 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq953
  have eq960 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq954
  have eq968 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq531
       have i₂ := eq960
       grind)
    | exact superpose eq960 eq531
    | exact resolve eq531 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq960
  have eq969 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq968
  have eq970 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq969
  have eq982 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq970
  have eq988 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq982
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq982
    | exact resolve eq982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1035 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq988
       grind)
    | exact superpose eq988 eq16
    | exact resolve eq16 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1035
       have i₂ := eq857 y x
       grind)
    | exact superpose eq857 eq1035
    | (have j1 := eq857 y x
       grind)
    | (have r₁ := eq1035
       have r₂ := eq857 y x
       grind)
    | exact resolve eq1035 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1044 : y = (M.op x x) := by grind
  clear eq1043
  have eq1080 : (M.op x y) = (k y x) := by grind
  clear eq1044
  have eq1085 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1035
       have i₂ := eq1080
       grind)
    | exact superpose eq1080 eq1035
    | exact resolve eq1035 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq1080
  have eq1088 : False := by grind
  exact eq1088

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
  have eq271 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq272 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq272 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq272 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq285 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq274 (σ X0)
       grind)
    | exact superpose eq274 eq15
    | exact resolve eq15 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq274 (τ X0)
       grind)
    | exact superpose eq274 eq31
    | exact resolve eq31 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq298 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq291 X0
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq291
    | exact resolve eq291 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq304 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq285
    | exact resolve eq285 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq285
  have eq349 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq352 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       have j1 := eq351 X0 X1
       grind)
    | (have r₁ := eq349 X0 X1
       have r₂ := eq351 X0 X1
       grind)
    | exact resolve eq349 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq351
  have eq365 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq368 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq365 X0 X1
       have j1 := eq367 X0 X1
       grind)
    | (have r₁ := eq365 X0 X1
       have r₂ := eq367 X0 X1
       grind)
    | exact resolve eq365 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq367
  have eq371 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq352 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq352
    | exact resolve eq352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352 x (σ y)
       grind)
    | exact superpose eq352 eq16
    | (have j1 := eq352 x (σ y)
       grind)
    | exact resolve eq16 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq352 X1 X0
       grind)
    | exact superpose eq352 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq352 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq352 X0 X1
       grind)
    | exact resolve eq13 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq383 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq377 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq384 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq383 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq383 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq385 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq375
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq375
    | exact resolve eq375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq389 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq371 X1 X0
       grind)
    | exact superpose eq371 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq371 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq371 X0 X1
       grind)
    | exact resolve eq13 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq400 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq389 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq402 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq400 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq400 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq416 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq402 X1 (τ X0)
       grind)
    | exact superpose eq402 eq18
    | (have j1 := eq402 X1 (τ X0)
       grind)
    | exact resolve eq18 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq433 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq402 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq1394 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq416 X1 (τ X0)
       grind)
    | exact superpose eq416 eq17
    | (have j1 := eq416 X1 (τ X0)
       grind)
    | exact resolve eq17 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq416
  have eq1401 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1394 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1394
    | (have j0 := eq1394 X0 X1
       grind)
    | exact resolve eq1394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1412 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1401 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1401
    | (have j0 := eq1401 X0 X1
       grind)
    | exact resolve eq1401 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1413 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1412
    | (have j0 := eq1412 X0 X1
       grind)
    | exact resolve eq1412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1473 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X0 (σ X1)
       have i₂ := eq384 X0 X1
       grind)
    | exact superpose eq384 eq1413
    | (have j0 := eq1413 X1 (σ X0)
       have j1 := eq384 X1 X0
       grind)
    | exact resolve eq1413 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq1413
  have eq1534 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1473 X0 X1
       have j1 := eq433 X1 (σ X0)
       grind)
    | (have r₁ := eq1473 X0 X0
       have r₂ := eq433 X0 (σ X0)
       grind)
    | exact resolve eq1473 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq1473
  have eq1555 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1534 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1534
    | (have j0 := eq1534 X0 X1
       grind)
    | exact resolve eq1534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq2373 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1555 X1 (σ X0)
       grind)
    | exact superpose eq1555 eq28
    | (have j1 := eq1555 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1555
  have eq2384 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2373 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2373
    | (have j0 := eq2373 X0 X1
       grind)
    | exact resolve eq2373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2373
  have eq2397 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2384 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2384
    | (have j0 := eq2384 X0 X1
       grind)
    | exact resolve eq2384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384
  have eq2406 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2397 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2397
    | (have j0 := eq2397 X0 X1
       grind)
    | exact resolve eq2397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2462 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2406 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2406
    | (have j0 := eq2406 X1 (τ X0)
       grind)
    | exact resolve eq2406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2484 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2406 y x
       grind)
    | exact superpose eq2406 eq16
    | (have j1 := eq2406 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2406 y x
       grind)
    | exact resolve eq16 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406
  have eq2519 : y = (k y x) := by grind
  clear eq2484
  have eq2748 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X1 X0
       have i₂ := eq2462 X1 X0
       grind)
    | exact superpose eq2462 eq368
    | (have j0 := eq368 X1 X0
       have j1 := eq2462 X1 X0
       grind)
    | exact resolve eq368 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq2462
  have eq2761 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2850 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2761 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2761
    | exact resolve eq2761 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761
  have eq2950 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2850 x y
       grind)
    | exact superpose eq2850 eq16
    | (have j1 := eq2850 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2850 x y
       grind)
    | exact resolve eq16 eq2850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2850
  have eq2987 : y = (M.op x y) := by grind
  clear eq2950
  have eq4477 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq385
       have i₂ := eq2987
       grind)
    | exact superpose eq2987 eq385
    | exact resolve eq385 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq4484 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq4477
  have eq4488 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4484
       have i₂ := eq2519
       grind)
    | exact superpose eq2519 eq4484
    | exact resolve eq4484 eq2519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519 eq4484
  have eq4496 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4488
       grind)
    | exact superpose eq4488 eq16
    | exact resolve eq16 eq4488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4488
  have eq4535 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4496
       have i₂ := eq2987
       grind)
    | exact superpose eq2987 eq4496
    | exact resolve eq4496 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987 eq4496
  have eq4536 : False := by grind
  exact eq4536

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2533 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq281 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq285 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq298 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq286
    | exact resolve eq286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286 x y
       grind)
    | exact superpose eq286 eq16
    | (have j1 := eq286 x y
       grind)
    | exact resolve eq16 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq318 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq298
    | (have j0 := eq298 X0 X1
       grind)
    | exact resolve eq298 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq298
  have eq323 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq318
    | exact resolve eq318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq304
       have i₂ := eq323 x y
       grind)
    | exact superpose eq323 eq304
    | (have j1 := eq323 (σ x) (σ y)
       grind)
    | (have r₁ := eq304
       have r₂ := eq323 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq304
       have r₂ := eq323 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq304 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq323
  have eq401 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq398
  have eq403 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq401
       grind)
    | exact superpose eq401 eq10
    | exact resolve eq10 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq436 : x = y ∨ x = y := by
    first
    | (have i₁ := eq403
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq403
    | exact resolve eq403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq437 : x = y := by grind
  clear eq436
  have eq476 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq437
       grind)
    | exact superpose eq437 eq16
    | exact resolve eq16 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq477 : False := by grind
  exact eq477

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq73
    | (have j0 := eq73 (σ X0) (σ X1)
       grind)
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq70
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq70 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq126 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq373 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq381 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq385 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq385
    | exact resolve eq385 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq389 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq390 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq373 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq373
    | exact resolve eq373 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq397 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq387 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq387
    | (have j0 := eq387 x y
       grind)
    | exact resolve eq387 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq89 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq105 eq73
    | (have j0 := eq73 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq682
    | exact resolve eq682 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq686 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq683
       have r₂ := eq28
       grind)
    | exact resolve eq683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq688 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq686 eq387
    | exact resolve eq387 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq686 eq14
    | exact resolve eq14 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq688 eq14
    | exact resolve eq14 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq691
    | (have j0 := eq691 (σ y)
       grind)
    | exact resolve eq691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq717 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq703 eq14
    | exact resolve eq14 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq736 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq702
    | (have j0 := eq702 (σ y)
       grind)
    | exact resolve eq702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq827 : (σ y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq688 eq717
    | exact resolve eq717 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq717
  have eq835 : (σ y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq827
  have eq850 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq736 eq835
    | exact resolve eq835 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq857 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq850
  have eq858 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq857
    | exact resolve eq857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq867 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq387 y y
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq387
    | exact resolve eq387 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 : G, y = (M.op (M.op y (M.op x X0)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq14
    | exact resolve eq14 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq14
    | exact resolve eq14 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq876 : y = (M.op (M.op y (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq870 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq870
    | (have j0 := eq870 y
       grind)
    | exact resolve eq870 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq890 : ∀ X0 : G, y = (M.op (M.op (M.op y (M.op x y)) (M.op y X0)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq876 eq14
    | exact resolve eq14 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq899 : x = (M.op (M.op y (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq875 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq875
    | (have j0 := eq875 y
       grind)
    | exact resolve eq875 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq909 : (M.op x y) = (M.op (M.op y x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq899 eq14
    | exact resolve eq14 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : x = (M.op (M.op (M.op y (M.op x y)) (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq909 eq381
    | exact resolve eq381 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1207 : y = (M.op (M.op (M.op y (M.op x y)) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq890 x
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq890
    | exact resolve eq890 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq890
  have eq1215 : y = (M.op (M.op (M.op y (M.op x y)) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1207
  have eq1217 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq899 eq1215
    | exact resolve eq1215 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1215
  have eq1225 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1217
  have eq1226 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1225
    | exact resolve eq1225 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1238 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1226 eq736
    | exact resolve eq736 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq1226
  have eq1803 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq686 eq1238
    | exact resolve eq1238 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq1238
  have eq1811 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1803
  have eq1816 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1811 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1811
       grind)
    | exact resolve eq13 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1827 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1827 eq105
    | exact resolve eq105 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1827
  have eq1920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1910
  have eq1925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq1920
    | exact resolve eq1920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq1927 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1925
       have r₂ := eq28
       grind)
    | exact resolve eq1925 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1941 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq387 y y
       have i₂ := eq1927
       grind)
    | exact superpose eq1927 eq387
    | exact resolve eq387 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq1944 : ∀ X0 : G, y = (M.op (M.op y (M.op x X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq1927
       grind)
    | exact superpose eq1927 eq14
    | exact resolve eq14 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq1954 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq14
    | exact resolve eq14 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1955 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1944 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1944
    | (have j0 := eq1944 y
       grind)
    | exact resolve eq1944 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq2018 : ∀ X0 : G, y = (M.op (M.op (M.op y (M.op x y)) (M.op y X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1955 eq14
    | exact resolve eq14 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq2028 : x = (M.op (M.op y (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1954 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1954
    | (have j0 := eq1954 y
       grind)
    | exact resolve eq1954 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq2496 : y = (M.op (M.op (M.op y (M.op x y)) x) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2018 x
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq2018
    | exact resolve eq2018 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941 eq2018
  have eq2505 : y = (M.op (M.op (M.op y (M.op x y)) x) y) ∨ y = (M.op x y) := by grind
  clear eq2496
  have eq2527 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2028 eq2505
    | exact resolve eq2505 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq2505
  have eq2536 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2527
  have eq2537 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2536
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2536
    | exact resolve eq2536 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2536
  have eq2538 : y = (M.op x y) := by grind
  clear eq2537
  have eq2539 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2538 eq21
    | exact resolve eq21 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2590 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2539
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2539
    | exact resolve eq2539 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2539
  have eq2591 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2590 eq27
    | exact resolve eq27 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2638 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y (M.op (M.op y X0) X1)) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq2538 eq389
    | exact resolve eq389 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq2671 : y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq53 y y x y
       have i₂ := eq2638 y x
       grind)
    | exact superpose eq2638 eq53
    | exact resolve eq53 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2638
  have eq2741 : (M.op (M.op y (M.op x y)) (M.op x y)) = (M.op (M.op (M.op y (M.op x y)) x) (M.op (M.op y (M.op x y)) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq932 eq390
    | exact resolve eq390 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq932
  have eq2957 : (M.op (M.op y y) y) = (M.op (M.op (M.op y y) x) (M.op (M.op y y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2538 eq2741
    | exact resolve eq2741 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq3008 : y = (M.op (M.op (M.op y y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2957
       have i₂ := eq2671
       grind)
    | exact superpose eq2671 eq2957
    | exact resolve eq2957 eq2671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957
  have eq3043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op (M.op y y) x) y) := by
    first
    | exact superpose eq2590 eq3008
    | exact resolve eq3008 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq3062 : y = (M.op (M.op (M.op y y) x) y) := by
    first
    | (have r₁ := eq3043
       have r₂ := eq28
       grind)
    | exact resolve eq3043 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq3072 : x = (M.op (M.op (M.op (M.op y y) y) (M.op x y)) x) := by
    first
    | (have i₁ := eq381 (M.op y y) y
       have i₂ := eq3062
       grind)
    | exact superpose eq3062 eq381
    | exact resolve eq381 eq3062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq3062
  have eq3084 : x = (M.op (M.op (M.op (M.op y y) y) y) x) := by
    first
    | exact superpose eq2538 eq3072
    | exact resolve eq3072 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538 eq3072
  have eq3086 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq3084
       have i₂ := eq2671
       grind)
    | exact superpose eq2671 eq3084
    | exact resolve eq3084 eq2671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671 eq3084
  have eq3105 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3086
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq3086
    | exact resolve eq3086 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq3086
  have eq3123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2590 eq3105
    | exact resolve eq3105 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq3105
  have eq3125 : x = (M.op x x) := by
    first
    | (have r₁ := eq3123
       have r₂ := eq28
       grind)
    | exact resolve eq3123 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq3138 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq3125
       grind)
    | exact superpose eq3125 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq3125
       grind)
    | exact resolve eq13 eq3125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3150 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq3138 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq3178 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq3150 x
       grind)
    | exact superpose eq3150 eq44
    | exact resolve eq44 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3184 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq3150 sF0
       grind)
    | exact superpose eq3150 eq126
    | exact resolve eq126 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq3150
  have eq3202 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq397 eq3184
    | exact resolve eq3184 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq3184
  have eq3204 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3178
       have i₂ := eq3125
       grind)
    | exact superpose eq3125 eq3178
    | exact resolve eq3178 eq3125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125 eq3178
  have eq3210 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq3202
    | exact resolve eq3202 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3202
  have eq3212 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3204
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3204
    | exact resolve eq3204 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204
  have eq3266 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq508 x
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq508
    | (have j0 := eq508 x
       grind)
    | exact resolve eq508 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq508
  have eq3272 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3212 eq3266
    | (have r₁ := eq3266
       have r₂ := eq3212
       grind)
    | exact resolve eq3266 eq3212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212 eq3266
  have eq3279 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq3272
       have r₂ := eq23
       grind)
    | exact resolve eq3272 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3285 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3279
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3279
    | exact resolve eq3279 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3279
  have eq3294 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq3285 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq3285
       grind)
    | exact resolve eq13 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq3306 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq3294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq3433 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3306 eq3210
    | exact resolve eq3210 eq3306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3210 eq3306
  have eq3465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2591 eq3433
    | exact resolve eq3433 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591 eq3433
  have eq3478 : False := by grind
  exact eq3478

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_y_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  clear eq39
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq181
    | (have j0 := eq181 X0
       grind)
    | exact resolve eq181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq542 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq544 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq549 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq551 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq549
    | exact resolve eq549 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq877 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq880 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq946 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq40
    | exact resolve eq40 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq947 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq946
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq946
    | exact resolve eq946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq949 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq947
    | exact resolve eq947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq949 eq880
    | exact resolve eq880 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq949
  have eq964 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq957
       have r₂ := eq27
       grind)
    | exact resolve eq957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq972 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq964 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq964
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq964
       grind)
    | exact resolve eq13 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq989 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq964
       have i₂ := eq973 sF3
       grind)
    | exact superpose eq973 eq964
    | exact resolve eq964 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq973
  have eq996 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq989
  have eq1002 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq996 eq152
    | exact resolve eq152 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq996
  have eq1007 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq1002
    | exact resolve eq1002 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1010 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq917 y
       grind)
    | (have r₁ := eq1007
       have r₂ := eq917 y
       grind)
    | exact resolve eq1007 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1017 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq16
    | exact resolve eq16 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1010
       grind)
    | exact resolve eq13 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1022 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1017 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq1017 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq1017
    | exact resolve eq1017 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq1017
  have eq1034 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1010
       have i₂ := eq1019 y
       grind)
    | exact superpose eq1019 eq1010
    | exact resolve eq1010 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1034
  have eq1055 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq40
    | exact resolve eq40 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1047
  have eq1060 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1055
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1055
    | exact resolve eq1055 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1066 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1060 eq917
    | (have j0 := eq917 (σ y)
       grind)
    | (have r₁ := eq917 (σ y)
       have r₂ := eq1060
       grind)
    | exact resolve eq917 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq1060
  have eq1067 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1066
  have eq1077 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1067 eq16
    | exact resolve eq16 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : (σ y) = (k (σ y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1067 eq1019
    | exact resolve eq1019 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1083 : (σ y) = (k (σ y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1078
  have eq1087 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq551 eq1077
    | exact resolve eq1077 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq1077
  have eq1103 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1022 X0
       grind)
    | exact superpose eq1022 eq16
    | exact resolve eq16 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1010 eq1103
    | exact resolve eq1103 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010 eq1103
  have eq1115 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1022 X0
       have i₂ := eq1110 X0
       grind)
    | exact superpose eq1110 eq1022
    | exact resolve eq1022 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1121 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y X1
       have i₂ := eq1110 (M.op (M.op y X0) X1)
       grind)
    | exact superpose eq1110 eq16
    | exact resolve eq16 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1129 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1110 eq1121
    | exact resolve eq1121 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq1121
  have eq1143 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1126 x
       grind)
    | exact superpose eq1126 eq18
    | (have j1 := eq1126 x
       grind)
    | exact resolve eq18 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1167 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1143 eq183
    | exact resolve eq183 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1373 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1393 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1393
    | exact resolve eq1393 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1563 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1087 eq16
    | exact resolve eq16 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1578 : ∀ X0 : G, (M.op (k (σ y) y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1019 eq1563
    | exact resolve eq1563 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq1563
  have eq1581 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1083 eq1578
    | exact resolve eq1578 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq1578
  have eq1601 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1581 eq1129
    | exact resolve eq1129 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq1581
  have eq1604 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1644 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1604 eq26
    | (have j1 := eq1604 (σ x)
       grind)
    | exact resolve eq26 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1665 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1644 eq27
    | exact resolve eq27 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq4316 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1167
    | (have j0 := eq1167 (σ y)
       grind)
    | exact resolve eq1167 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4361 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1143 eq4316
    | exact resolve eq4316 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316
  have eq4372 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4361 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq4361
       grind)
    | exact resolve eq13 eq4361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4382 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4372 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4372
  have eq4475 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4361
       have i₂ := eq4382 sF2
       grind)
    | exact superpose eq4382 eq4361
    | exact resolve eq4361 eq4382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361
  have eq4476 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1167 sF2
       have i₂ := eq4382 sF2
       grind)
    | exact superpose eq4382 eq1167
    | exact resolve eq1167 eq4382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq4485 : (σ y) = (M.op (M.op (σ x) (k (M.op (σ x) (σ y)) (σ x))) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 sF4
       have i₂ := eq4382 sF4
       grind)
    | exact superpose eq4382 eq175
    | exact resolve eq175 eq4382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4382
  have eq4490 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4476
  have eq4491 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4475
  have eq4549 : (σ y) = (M.op (M.op (σ x) (k (σ x) (σ x))) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1143 eq4485
    | exact resolve eq4485 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq4556 : (σ y) = (M.op (k (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4490 eq4549
    | exact resolve eq4549 eq4490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4490 eq4549
  have eq4558 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4491 eq4556
    | exact resolve eq4556 eq4491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4491 eq4556
  have eq4559 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4558
    | exact resolve eq4558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558
  have eq4560 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1143 eq4559
    | exact resolve eq4559 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4562 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4560 eq31
    | exact resolve eq31 eq4560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4560
  have eq4669 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq4562
    | exact resolve eq4562 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4562
  have eq4674 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq4669
       grind)
    | exact superpose eq4669 eq24
    | exact resolve eq24 eq4669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4669
  have eq4713 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq4674
    | exact resolve eq4674 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4674
  have eq4729 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4713 eq1665
    | (have r₁ := eq1665
       have r₂ := eq4713
       grind)
    | exact resolve eq1665 eq4713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665 eq4713
  have eq4782 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4729
  have eq4783 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4782
  have eq4788 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1143 eq4783
    | exact resolve eq4783 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq4783
  have eq4789 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4788
  have eq4804 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4789 eq27
    | exact resolve eq27 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4805 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4789 eq175
    | exact resolve eq175 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4812 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4805 X0
       have i₂ := eq1399 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq4805 x
       have i₂ := eq1399 sF2 x
       grind)
    | exact superpose eq1399 eq4805
    | exact resolve eq4805 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4805
  have eq4820 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4812
    | (have j0 := eq4812 (σ y)
       grind)
    | exact resolve eq4812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4841 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4812 eq176
    | exact resolve eq176 eq4812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4842 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4812 eq16
    | exact resolve eq16 eq4812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4812
  have eq4874 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4842
    | (have j0 := eq4842 X0
       grind)
    | exact resolve eq4842 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842
  have eq4875 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq4841
    | (have j0 := eq4841 X0 X1
       grind)
    | exact resolve eq4841 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841
  have eq4880 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4789 eq4820
    | exact resolve eq4820 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4820
  have eq4882 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4789 eq4874
    | exact resolve eq4874 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4874
  have eq4883 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4789 eq4875
    | exact resolve eq4875 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4875
  have eq4887 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4880
    | exact resolve eq4880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4880
  have eq4889 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4882 eq4883
    | exact resolve eq4883 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4883
  have eq4892 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4789 eq4887
    | exact resolve eq4887 eq4789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4789 eq4887
  have eq5328 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4882 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq4882 (σ x)
       grind)
    | exact resolve eq13 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5349 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5612 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq4889 X0 X1
       grind)
    | exact superpose eq4889 eq16
    | exact resolve eq16 eq4889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4889
  have eq5684 : ∀ X0 X1 : G, (M.op (k X0 (σ x)) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5349 eq5612
    | exact resolve eq5612 eq5349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612
  have eq5802 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1399 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1399
    | (have j0 := eq1399 x y
       grind)
    | exact resolve eq1399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6122 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4882 sF2
       have i₂ := eq5349 sF2
       grind)
    | exact superpose eq5349 eq4882
    | exact resolve eq4882 eq5349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4882
  have eq6140 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6122
  have eq6218 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6140 eq141
    | exact resolve eq141 eq6140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq6140
  have eq6228 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq6218
    | exact resolve eq6218 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6218
  have eq6237 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq915 x x
       have i₂ := eq6228
       grind)
    | exact superpose eq6228 eq915
    | (have j0 := eq915 x x
       grind)
    | (have r₁ := eq915 x x
       have r₂ := eq6228
       grind)
    | exact resolve eq915 eq6228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6228
  have eq6238 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6237
  have eq6239 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6238
  have eq6260 : x = (k x (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5349 x
       have i₂ := eq6239
       grind)
    | exact superpose eq6239 eq5349
    | exact resolve eq5349 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349 eq6239
  have eq6276 : x = (k x (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6260
  have eq6321 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6276 eq5684
    | exact resolve eq5684 eq6276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5684 eq6276
  have eq6377 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6321 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6321
  have eq6410 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6377 y
       grind)
    | exact superpose eq6377 eq18
    | (have j1 := eq6377 y
       grind)
    | exact resolve eq18 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6377
  have eq6483 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq24
    | exact resolve eq24 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6410
  have eq6523 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6483
    | exact resolve eq6483 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6483
  have eq6526 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4892 eq6523
    | exact resolve eq6523 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892 eq6523
  have eq6527 : x = (M.op x y) := by
    first
    | (have r₁ := eq6526
       have r₂ := eq4804
       grind)
    | exact resolve eq6526 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804 eq6526
  have eq6528 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6527
       grind)
    | exact superpose eq6527 eq18
    | exact resolve eq18 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6529 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6527
       grind)
    | exact superpose eq6527 eq22
    | exact resolve eq22 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6539 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6529 eq20
    | exact resolve eq20 eq6529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6682 : y = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq6528 eq174
    | exact resolve eq174 eq6528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq6695 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6528 eq1399
    | exact resolve eq1399 eq6528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq6703 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq5802 eq6682
    | exact resolve eq6682 eq5802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5802 eq6682
  have eq6706 : y = (M.op x y) := by
    first
    | exact superpose eq6528 eq6703
    | exact resolve eq6703 eq6528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528 eq6703
  have eq6708 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6706
       grind)
    | exact superpose eq6706 eq24
    | exact resolve eq24 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6706
  have eq6735 : (σ x) = (σ y) := by
    first
    | exact superpose eq6529 eq6708
    | exact resolve eq6708 eq6529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6529 eq6708
  have eq6738 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6735 eq26
    | exact resolve eq26 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6735
  have eq6845 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6695 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq6695
       grind)
    | exact resolve eq13 eq6695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6695
  have eq6863 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq6845 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq7085 : ∀ X0 X1 : G, x = (k (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) ∨ (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq1373 X0 X1
       have i₂ := eq11 (M.op (M.op X0 (M.op (M.op X0 x) X1)) sF0) x
       grind)
    | exact superpose eq11 eq1373
    | (have j1 := eq11 (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x
       grind)
    | exact resolve eq1373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq7119 : ∀ X0 X1 : G, x = (k (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq7085 X0 X1
       have j1 := eq12 (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x
       grind)
    | (have r₁ := eq7085 X0 X1
       have r₂ := eq12 (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x
       grind)
    | (have r₁ := eq7085 X0 X1
       have r₂ := eq12 x x
       grind)
    | exact resolve eq7085 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7085
  have eq7142 : ∀ X0 X1 : G, (M.op x y) = (k (M.op (M.op X0 (M.op (M.op X0 (M.op x y)) X1)) (M.op x y)) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq7119 X0 X1
       have i₂ := eq6527
       grind)
    | exact superpose eq6527 eq7119
    | exact resolve eq7119 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7119
  have eq7162 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7142 x x
       have i₂ := eq16 sF0 x x
       grind)
    | exact superpose eq16 eq7142
    | exact resolve eq7142 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7142
  have eq7175 : x = (k x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7162
       have i₂ := eq6863 x
       grind)
    | exact superpose eq6863 eq7162
    | exact resolve eq7162 eq6863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7162
  have eq7187 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7175
       have i₂ := eq6527
       grind)
    | exact superpose eq6527 eq7175
    | exact resolve eq7175 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6527 eq7175
  have eq7188 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq7187
  have eq7325 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7188 eq37
    | exact resolve eq37 eq7188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7188
  have eq7339 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq7325
    | exact resolve eq7325 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7325
  have eq7341 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6539 eq7339
    | exact resolve eq7339 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7339
  have eq7350 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7341 eq915
    | (have j0 := eq915 (σ x) (σ x)
       grind)
    | (have r₁ := eq915 (σ x) (σ x)
       have r₂ := eq7341
       grind)
    | exact resolve eq915 eq7341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq7341
  have eq7351 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7350
  have eq7352 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7351
  have eq7356 : (σ x) = (k (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq7352
       have i₂ := eq6863 sF2
       grind)
    | exact superpose eq6863 eq7352
    | exact resolve eq7352 eq6863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352
  have eq8161 : (M.op (σ x) (σ y)) = (k (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq6738
       have i₂ := eq6863 sF2
       grind)
    | exact superpose eq6863 eq6738
    | exact resolve eq6738 eq6863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6738 eq6863
  have eq8181 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7356 eq8161
    | exact resolve eq8161 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356 eq8161
  have eq8199 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8181 eq27
    | exact resolve eq27 eq8181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8181
  have eq8212 : False := by grind
  exact eq8212

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_y_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 X0
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq344 : ∀ X0 : G, (k (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (k X0 (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq133 eq38
    | exact resolve eq38 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq133
  have eq542 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq544 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq886 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq905 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq916 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq919 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq920 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq919 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq919 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq919 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq923 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq920 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq920
    | (have j0 := eq920 (σ X0) X1
       grind)
    | exact resolve eq920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1789 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1803 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1811 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1815 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1811 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1811
    | exact resolve eq1811 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1820 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1789 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1789
    | exact resolve eq1789 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq1860 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1815 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1815
    | (have j0 := eq1815 x y
       grind)
    | exact resolve eq1815 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6182 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq895
       grind)
    | exact superpose eq895 eq39
    | exact resolve eq39 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq6183 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6182
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6182
    | exact resolve eq6182 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6182
  have eq6187 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq6183
    | exact resolve eq6183 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6183
  have eq15165 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1820 X0 X0 x
       grind)
    | exact superpose eq1820 eq176
    | exact resolve eq176 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15203 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq1803 x x
       have i₂ := eq15165 x
       grind)
    | exact superpose eq15165 eq1803
    | exact resolve eq1803 eq15165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15205 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1820 X0 X0 X0
       have i₂ := eq15165 X0
       grind)
    | exact superpose eq15165 eq1820
    | exact resolve eq1820 eq15165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15221 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1820 (M.op X0 X0) X0 x
       have i₂ := eq15165 X0
       grind)
    | exact superpose eq15165 eq1820
    | exact resolve eq1820 eq15165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15165
  have eq15438 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq15205 X0
       grind)
    | exact superpose eq15205 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq15205 X0
       grind)
    | exact resolve eq13 eq15205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15447 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15438 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15438
  have eq15468 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15447 X2 X0
       have i₂ := eq15447 X1 X0
       grind)
    | exact superpose eq15447 eq15447
    | exact resolve eq15447 eq15447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15492 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15205 X0
       have i₂ := eq15447 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15447 eq15205
    | exact resolve eq15205 eq15447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15205
  have eq15713 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k (M.op X0 X0) (M.op X1 X1))) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq923 (M.op X0 X0) X2
       have i₂ := eq15468 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq923 (M.op X0 X0) X2
       have i₂ := eq15468 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq15468 eq923
    | (have j0 := eq923 (M.op X0 X0) X2
       grind)
    | exact resolve eq923 eq15468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq15795 : ∀ X0 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq15713 X0 x X2
       have i₂ := eq15492 X0 x
       grind)
    | exact superpose eq15492 eq15713
    | (have j0 := eq15713 X0 x X2
       grind)
    | exact resolve eq15713 eq15492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15713
  have eq15796 : ∀ X0 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq15795 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15795
  have eq15947 : ∀ X0 : G, (k (M.op x y) (M.op X0 X0)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 X0)
       have i₂ := eq15796 X0 sF1
       grind)
    | exact superpose eq15796 eq50
    | exact resolve eq50 eq15796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq15957 : ∀ X0 : G, (k x (M.op X0 X0)) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq44 (M.op X0 X0)
       have i₂ := eq15796 X0 sF2
       grind)
    | exact superpose eq15796 eq44
    | exact resolve eq44 eq15796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq15967 : ∀ X0 : G, (k y (M.op X0 X0)) = (τ (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 X0)
       have i₂ := eq15796 X0 sF3
       grind)
    | exact superpose eq15796 eq47
    | exact resolve eq47 eq15796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq15796
  have eq15985 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq15967 x
       have i₂ := eq15447 x y
       grind)
    | exact superpose eq15447 eq15967
    | exact resolve eq15967 eq15447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15967
  have eq15995 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq15957 x
       have i₂ := eq15447 x x
       grind)
    | exact superpose eq15447 eq15957
    | exact resolve eq15957 eq15447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15957
  have eq16005 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq15947 x
       have i₂ := eq15447 x sF0
       grind)
    | exact superpose eq15447 eq15947
    | exact resolve eq15947 eq15447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15947
  have eq16053 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq15985 eq14
    | exact resolve eq14 eq15985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15985
  have eq16109 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15995
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq15995
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq15995 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16110 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq15995 eq14
    | exact resolve eq14 eq15995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16146 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16109
  have eq16168 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq97 eq16146
    | exact resolve eq16146 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq16146
  have eq16473 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16110
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq16110
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq16110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16110
  have eq16552 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq16473
  have eq16613 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16552
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq16552
    | exact resolve eq16552 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16552
  have eq16650 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16613
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16613
    | exact resolve eq16613 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16613
  have eq17363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6187 eq905
    | exact resolve eq905 eq6187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq17374 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17363
       have r₂ := eq27
       grind)
    | exact resolve eq17363 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363
  have eq17380 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (k x x) := by
    first
    | exact superpose eq16168 eq17374
    | exact resolve eq17374 eq16168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16168 eq17374
  have eq17420 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (k x x) := by
    first
    | exact superpose eq17380 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17380
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq17380
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17380
       grind)
    | exact resolve eq12 eq17380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17380
  have eq17433 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (k x x) := by grind
  clear eq17420
  have eq17434 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (k x x) := by grind
  clear eq17433
  have eq17539 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (k x x) := by
    first
    | exact superpose eq17434 eq6187
    | exact resolve eq6187 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6187 eq17434
  have eq17552 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by grind
  clear eq17539
  have eq17560 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq917 x
       grind)
    | (have r₁ := eq17552
       have r₂ := eq917 x
       grind)
    | exact resolve eq17552 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17552
  have eq17563 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16650 eq17560
    | exact resolve eq17560 eq16650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650 eq17560
  have eq17569 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17563 eq141
    | exact resolve eq141 eq17563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq17563
  have eq17583 : x = (k x x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq17569
    | exact resolve eq17569 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17569
  have eq17589 : y = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq917 x
       grind)
    | (have r₁ := eq17583
       have r₂ := eq917 x
       grind)
    | exact resolve eq17583 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq17583
  have eq17606 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1815 y x
       have i₂ := eq17589
       grind)
    | exact superpose eq17589 eq1815
    | exact resolve eq1815 eq17589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17607 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1820 y x x
       have i₂ := eq17589
       grind)
    | exact superpose eq17589 eq1820
    | exact resolve eq1820 eq17589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17613 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq17607 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq17607 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq17607
    | exact resolve eq17607 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq17607
  have eq17832 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq17613 X0
       grind)
    | exact superpose eq17613 eq16
    | exact resolve eq16 eq17613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17613
  have eq17860 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq17606 eq17832
    | exact resolve eq17832 eq17606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17606 eq17832
  have eq17867 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) x) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq15203
       have i₂ := eq17860 X0
       grind)
    | exact superpose eq17860 eq15203
    | (have j1 := eq17860 X0
       grind)
    | exact resolve eq15203 eq17860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15203
  have eq17913 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1860 eq17867
    | (have j0 := eq17867 X0
       grind)
    | exact resolve eq17867 eq1860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860 eq17867
  have eq17980 : ∀ X0 : G, y = (M.op (M.op x x) y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq17913 (M.op sF0 X0)
       grind)
    | exact superpose eq17913 eq174
    | (have j1 := eq17913 X0
       grind)
    | exact resolve eq174 eq17913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17913
  have eq17998 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq17860 eq17980
    | (have j0 := eq17980 X0
       have j1 := eq17860 X0
       grind)
    | exact resolve eq17980 eq17860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17860 eq17980
  have eq18004 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq17998 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17998
    | (have j0 := eq17998 X0
       grind)
    | exact resolve eq17998 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17998
  have eq18047 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y X1
       have i₂ := eq18004 (M.op (M.op y X0) X1)
       grind)
    | exact superpose eq18004 eq16
    | exact resolve eq16 eq18004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18063 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq18004 eq18047
    | exact resolve eq18047 eq18004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18047
  have eq18547 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq18063 y X0
       have i₂ := eq18004 X0
       grind)
    | exact superpose eq18004 eq18063
    | exact resolve eq18063 eq18004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18004 eq18063
  have eq18600 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq18547 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18547
  have eq19116 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18600 x
       grind)
    | exact superpose eq18600 eq18
    | (have j1 := eq18600 x
       grind)
    | exact resolve eq18 eq18600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18600
  have eq19136 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq19116
  have eq19152 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19136 eq28
    | exact resolve eq28 eq19136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq19199 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19136 eq16005
    | exact resolve eq16005 eq19136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19136
  have eq19200 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15995 eq19199
    | exact resolve eq19199 eq15995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15995 eq19199
  have eq19247 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19152
    | exact resolve eq19152 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19152
  have eq19261 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19247
       grind)
    | exact superpose eq19247 eq24
    | exact resolve eq24 eq19247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19308 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19261
    | exact resolve eq19261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19261
  have eq19419 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X0)) (M.op x y)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1803 x X0
       have i₂ := eq19200
       grind)
    | exact superpose eq19200 eq1803
    | exact resolve eq1803 eq19200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19200
  have eq19478 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) X0)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19247 eq19419
    | exact resolve eq19419 eq19247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19419
  have eq19489 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19478 x
       have i₂ := eq16 sF0 sF0 x
       grind)
    | exact superpose eq16 eq19478
    | exact resolve eq19478 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19478
  have eq19547 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19489 eq1820
    | exact resolve eq1820 eq19489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19555 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq180 eq19547
    | exact resolve eq19547 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq19547
  have eq20827 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19555 eq16
    | exact resolve eq16 eq19555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19555
  have eq20866 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19489 eq20827
    | exact resolve eq20827 eq19489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19489 eq20827
  have eq20876 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20866 eq174
    | exact resolve eq174 eq20866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq20968 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19247 eq20876
    | exact resolve eq20876 eq19247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19247 eq20876
  have eq20984 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20866 eq20968
    | exact resolve eq20968 eq20866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20866 eq20968
  have eq21224 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20984 x
       grind)
    | exact superpose eq20984 eq18
    | (have j1 := eq20984 x
       grind)
    | exact resolve eq18 eq20984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20984
  have eq21247 : y = (M.op x y) := by grind
  clear eq21224
  have eq21264 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq21247
       grind)
    | exact superpose eq21247 eq24
    | exact resolve eq24 eq21247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq21287 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16053
       have i₂ := eq21247
       grind)
    | exact superpose eq21247 eq16053
    | exact resolve eq16053 eq21247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16053
  have eq21288 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17589
       have i₂ := eq21247
       grind)
    | exact superpose eq21247 eq17589
    | exact resolve eq17589 eq21247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17589
  have eq21300 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21264 eq20
    | exact resolve eq20 eq21264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21303 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq21264 eq15
    | exact resolve eq15 eq21264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21566 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq21300 eq16005
    | exact resolve eq16005 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16005
  have eq21725 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq21287
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq21287
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq21287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21810 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq21725
  have eq21882 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41 eq21810
    | exact resolve eq21810 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21810
  have eq21943 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21300 eq21882
    | exact resolve eq21882 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21882
  have eq21983 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq21943
    | exact resolve eq21943 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21943
  have eq22008 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21300 eq21983
    | exact resolve eq21983 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21983
  have eq27187 : (τ (k (σ y) (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq22008 eq21566
    | exact resolve eq21566 eq22008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21566 eq22008
  have eq27246 : (k y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq115 eq27187
    | exact resolve eq27187 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq27187
  have eq27253 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq27246
       have i₂ := eq21247
       grind)
    | exact superpose eq21247 eq27246
    | exact resolve eq27246 eq21247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21247 eq27246
  have eq27258 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq27253
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq27253 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27253
  have eq27265 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27258 eq21287
    | exact resolve eq21287 eq27258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21287
  have eq27284 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27258 eq15447
    | exact resolve eq15447 eq27258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15447
  have eq27286 : ∀ X0 X1 : G, (k X0 (k (M.op x y) (M.op x y))) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq27258 eq15468
    | exact resolve eq15468 eq27258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27258
  have eq27339 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41 eq27265
    | exact resolve eq27265 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq27265
  have eq27349 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21300 eq27339
    | exact resolve eq27339 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27339
  have eq27357 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq27349
    | exact resolve eq27349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27349
  have eq27365 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21300 eq27357
    | exact resolve eq27357 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27357
  have eq27423 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ y))) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq27365 eq15468
    | exact resolve eq15468 eq27365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15468
  have eq27427 : ∀ X0 : G, (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq27365 eq15492
    | exact resolve eq15492 eq27365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15492 eq27365
  have eq27471 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq27427 x
       have i₂ := eq27286 (k sF3 sF3) x
       grind)
    | exact superpose eq27286 eq27427
    | exact resolve eq27427 eq27286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27427
  have eq27472 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (k X0 (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq27423 X0 x
       have i₂ := eq27286 X0 x
       grind)
    | exact superpose eq27286 eq27423
    | exact resolve eq27423 eq27286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27286 eq27423
  have eq27605 : ∀ X0 X1 : G, (M.op (M.op (k X0 (k (M.op x y) (M.op x y))) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15221 X0 X1
       have i₂ := eq27284 X0
       grind)
    | exact superpose eq27284 eq15221
    | exact resolve eq15221 eq27284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15221
  have eq27674 : ∀ X0 : G, (k (σ X0) (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq27284 eq344
    | exact resolve eq344 eq27284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq27707 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq21300 eq27674
    | exact resolve eq27674 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27674
  have eq27736 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27472 eq27707
    | exact resolve eq27707 eq27472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27472 eq27707
  have eq32666 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq27736 eq27284
    | exact resolve eq27284 eq27736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27736
  have eq68600 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op (k (σ y) (σ y)) (M.op (k (σ y) (σ y)) X0)) (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq27471 eq27605
    | exact resolve eq27605 eq27471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27605
  have eq68950 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op (k (σ y) (σ y)) X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq68600 X0
       have i₂ := eq1815 (k sF3 sF3) (M.op (k sF3 sF3) X0)
       grind)
    | (have i₁ := eq68600 x
       have i₂ := eq1815 (k sF3 sF3) x
       grind)
    | exact superpose eq1815 eq68600
    | exact resolve eq68600 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq68600
  have eq78845 : x = (M.op (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op x y)) x) := by
    first
    | exact superpose eq68950 eq1803
    | exact resolve eq1803 eq68950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq78847 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq68950 eq16
    | exact resolve eq16 eq68950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68950
  have eq78932 : ∀ X0 : G, (M.op (k (k (σ y) (σ y)) (k (M.op x y) (M.op x y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78847 X0
       have i₂ := eq27284 (k sF3 sF3)
       grind)
    | exact superpose eq27284 eq78847
    | exact resolve eq78847 eq27284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78847
  have eq78934 : x = (M.op (M.op (k (k (σ y) (σ y)) (k (M.op x y) (M.op x y))) (M.op x y)) x) := by
    first
    | (have i₁ := eq78845
       have i₂ := eq27284 (k sF3 sF3)
       grind)
    | exact superpose eq27284 eq78845
    | exact resolve eq78845 eq27284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27284 eq78845
  have eq78953 : ∀ X0 : G, (M.op (k (σ y) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27471 eq78932
    | exact resolve eq78932 eq27471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78932
  have eq78955 : x = (M.op (M.op (k (σ y) (σ y)) (M.op x y)) x) := by
    first
    | exact superpose eq27471 eq78934
    | exact resolve eq78934 eq27471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27471 eq78934
  have eq78964 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq78953 eq78955
    | exact resolve eq78955 eq78953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78955
  have eq79025 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq78964 eq21288
    | exact resolve eq21288 eq78964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21288
  have eq79095 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21300 eq79025
    | exact resolve eq79025 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79025
  have eq79226 : ∀ X0 X1 : G, (M.op (k (σ y) (σ y)) X0) = (M.op (M.op (M.op (k (σ y) (σ y)) X0) X1) (M.op (k (σ y) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq78953 eq1820
    | exact resolve eq1820 eq78953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq79259 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq78953 eq79226
    | exact resolve eq79226 eq78953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78953 eq79226
  have eq79936 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq79259 X0 X1
       grind)
    | exact superpose eq79259 eq16
    | exact resolve eq16 eq79259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79259
  have eq80096 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79936 (σ X0) X1
       have i₂ := eq32666 X0
       grind)
    | exact superpose eq32666 eq79936
    | exact resolve eq79936 eq32666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32666 eq79936
  have eq93803 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq80096 x X0
       have i₂ := eq79095
       grind)
    | exact superpose eq79095 eq80096
    | exact resolve eq80096 eq79095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79095
  have eq93857 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq93803 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq93803
    | (have j0 := eq93803 X0
       grind)
    | exact resolve eq93803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93803
  have eq104090 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq93857 eq26
    | (have j1 := eq93857 (σ y)
       grind)
    | exact resolve eq26 eq93857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93857
  have eq104347 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq104090 eq27
    | exact resolve eq27 eq104090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104090
  have eq104395 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq104347
       have r₂ := eq19308
       grind)
    | exact resolve eq104347 eq19308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19308 eq104347
  have eq104475 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104395 eq21303
    | exact resolve eq21303 eq104395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21303 eq104395
  have eq104569 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq104475
    | exact resolve eq104475 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq104475
  have eq104570 : x = (M.op x y) := by grind
  clear eq104569
  have eq104636 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq104570
       grind)
    | exact superpose eq104570 eq22
    | exact resolve eq22 eq104570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq104696 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq78964
       have i₂ := eq104570
       grind)
    | exact superpose eq104570 eq78964
    | exact resolve eq78964 eq104570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78964 eq104570
  have eq104766 : (σ x) = (σ y) := by
    first
    | exact superpose eq104636 eq21264
    | exact resolve eq21264 eq104636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21264
  have eq104767 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq104636 eq20
    | exact resolve eq20 eq104636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104636
  have eq105877 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq104696 eq80096
    | exact resolve eq80096 eq104696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80096 eq104696
  have eq105940 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq105877
    | (have j0 := eq105877 X0
       grind)
    | exact resolve eq105877 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq105877
  have eq105975 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq21300 eq105940
    | exact resolve eq105940 eq21300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21300 eq105940
  have eq105998 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq104766 eq105975
    | exact resolve eq105975 eq104766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105975
  have eq110642 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105998 eq26
    | (have j1 := eq105998 (σ y)
       grind)
    | exact resolve eq26 eq105998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq105998
  have eq110854 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104766 eq110642
    | exact resolve eq110642 eq104766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104766 eq110642
  have eq110972 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq110854 eq27
    | exact resolve eq27 eq110854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq110854
  have eq111020 : False := by grind
  exact eq111020
