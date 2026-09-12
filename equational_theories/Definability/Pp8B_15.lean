import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyy_x_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq132 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
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
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 x X2
       have i₂ := eq177 X0 x X1
       grind)
    | (have i₁ := eq177 X2 X2 X2
       have i₂ := eq177 X2 X1 X2
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 x
       have i₂ := eq177 X1 X0 x
       grind)
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq177 X0 X0 X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq180 eq553
    | exact resolve eq553 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq932 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op X0 X2) X0) (M.op (M.op X0 X2) X0)) ∨ (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X1) (M.op (M.op X0 X2) X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 (M.op X1 X1) (M.op (M.op X0 X2) X0)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (M.op (M.op (M.op X1 X1) X2) (M.op X1 X1))
       have r₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq976 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1404 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq974
       grind)
    | exact superpose eq974 eq40
    | exact resolve eq40 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1405 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1404
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1404
    | exact resolve eq1404 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1407 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1405
    | exact resolve eq1405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1422 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq540 X3 X1 x
       have i₂ := eq540 X0 X1 x
       grind)
    | (have i₁ := eq540 X0 X1 X3
       have i₂ := eq540 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq540 eq540
    | exact resolve eq540 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq540 X0 (M.op X1 X1) X3
       have i₂ := eq540 X0 X1 X1
       grind)
    | (have i₁ := eq540 X0 (M.op X1 X1) X3
       have i₂ := eq540 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq540 eq540
    | exact resolve eq540 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) X3
       have i₂ := eq540 X0 X1 X1
       grind)
    | (have i₁ := eq16 X0 (M.op X1 X1) X2
       have i₂ := eq540 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq540 eq16
    | exact resolve eq16 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1578 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1435 X0 X1 x X3
       have i₂ := eq176 X0 x X1
       grind)
    | exact superpose eq176 eq1435
    | exact resolve eq1435 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1435
  have eq2132 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq1578 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq1578 eq13
    | exact resolve eq13 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1407 eq976
    | exact resolve eq976 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2439 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2432
       have r₂ := eq27
       grind)
    | exact resolve eq2432 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432
  have eq2557 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2439 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq2439
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2439
       grind)
    | exact resolve eq13 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2600 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq2557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2629 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2600 eq107
    | exact resolve eq107 eq2600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2600
  have eq2635 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq2629
    | exact resolve eq2629 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2629
  have eq2645 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1040 y
       grind)
    | (have r₁ := eq2635
       have r₂ := eq1040 y
       grind)
    | exact resolve eq2635 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq2635
  have eq2650 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq13
    | (have r₁ := eq13 X0 y
       have r₂ := eq2645
       grind)
    | exact resolve eq13 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2679 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1422 X0 y x
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq1422
    | exact resolve eq1422 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2693 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2650 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650
  have eq2711 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq2693 y
       grind)
    | exact superpose eq2693 eq36
    | exact resolve eq36 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2693
  have eq2720 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2711
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2711
    | exact resolve eq2711 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2737 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2720 eq1038
    | (have j0 := eq1038 (σ y) (σ y)
       grind)
    | (have r₁ := eq1038 (σ y) (σ y)
       have r₂ := eq2720
       grind)
    | exact resolve eq1038 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq2720
  have eq2738 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2737
  have eq2739 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2738
  have eq2824 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2739 eq1422
    | exact resolve eq1422 eq2739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3054 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq2679 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq2679 x X0
       grind)
    | exact superpose eq2679 eq18
    | (have j1 := eq2679 X0 x
       grind)
    | exact resolve eq18 eq2679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679
  have eq3235 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2645
       have i₂ := eq3054 y
       grind)
    | exact superpose eq3054 eq2645
    | exact resolve eq2645 eq3054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645 eq3054
  have eq3241 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3235
  have eq3269 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3241 eq27
    | exact resolve eq27 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3270 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3241 eq175
    | exact resolve eq175 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3275 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3241 eq932
    | (have r₁ := eq932
       have r₂ := eq3241
       grind)
    | exact resolve eq932 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq3281 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3275
  have eq3289 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3270 x
       have i₂ := eq542 sF2 x
       grind)
    | exact superpose eq542 eq3270
    | exact resolve eq3270 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270
  have eq5862 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2824 eq26
    | (have j1 := eq2824 X0 (σ x)
       grind)
    | exact resolve eq26 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5864 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2824 eq2739
    | exact resolve eq2739 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739 eq2824
  have eq5869 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5864
  have eq5896 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5869 eq5862
    | (have j1 := eq5869 (σ x)
       grind)
    | exact resolve eq5862 eq5869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5862 eq5869
  have eq6042 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5896 eq27
    | exact resolve eq27 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5896
  have eq6111 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq936 (M.op X0 X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq6113 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6111 X0 X1
       have i₂ := eq1462 (M.op (M.op X0 X0) X1) X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq1462 eq6111
    | (have j0 := eq6111 X0 X1
       grind)
    | exact resolve eq6111 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462 eq6111
  have eq6133 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6113 X0 X1
       have j1 := eq2132 X0 (M.op (M.op X0 X0) X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq6113 X0 X1
       have r₂ := eq2132 X0 (M.op (M.op X0 X0) X1) x
       grind)
    | exact resolve eq6113 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132 eq6113
  have eq6153 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6133 X0 x
       have i₂ := eq710 X0 x
       grind)
    | exact superpose eq710 eq6133
    | exact resolve eq6133 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq6133
  have eq6835 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3289 eq1422
    | exact resolve eq1422 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq7297 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) X1)) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6835 eq560
    | exact resolve eq560 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7321 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6835 eq1578
    | exact resolve eq1578 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7328 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6835 eq177
    | exact resolve eq177 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7330 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6835 eq553
    | exact resolve eq553 eq6835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq6835
  have eq7398 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) X1)) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq7328 eq7297
    | exact resolve eq7297 eq7328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7297 eq7328
  have eq9414 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq7398
    | (have j0 := eq7398 (σ y)
       grind)
    | exact resolve eq7398 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7398
  have eq9498 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3241 eq9414
    | exact resolve eq9414 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9414
  have eq9510 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9498 eq7321
    | exact resolve eq7321 eq9498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7321 eq9498
  have eq9572 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9510
  have eq9801 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (σ x) = (k X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9572 eq13
    | exact resolve eq13 eq9572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9844 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ (σ x) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9572 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq9572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9921 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9572 eq9844
    | (have j0 := eq9844 X0
       grind)
    | exact resolve eq9844 eq9572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844
  have eq9928 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ (σ x) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9921 X0
       have j1 := eq9801 X0
       grind)
    | (have r₁ := eq9921 (σ y)
       have r₂ := eq9801 X0
       grind)
    | (have r₁ := eq9921 X0
       have r₂ := eq9801 X0
       grind)
    | exact resolve eq9921 eq9801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9921
  have eq13029 : (τ (σ x)) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9928 eq132
    | (have j1 := eq9928 (σ (M.op x y))
       grind)
    | exact resolve eq132 eq9928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9928
  have eq13045 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13029
       have r₂ := eq3269
       grind)
    | exact resolve eq13029 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13029
  have eq13054 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq13045
    | exact resolve eq13045 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13045
  have eq13061 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13054 eq40
    | exact resolve eq40 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq13066 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq13061
    | exact resolve eq13061 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13061
  have eq13068 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13066
    | exact resolve eq13066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13066
  have eq31776 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3281 eq9572
    | exact resolve eq9572 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281 eq9572
  have eq31865 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq31776
  have eq31906 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq9801 (σ x)
       grind)
    | (have r₁ := eq31865
       have r₂ := eq9801 x
       grind)
    | exact resolve eq31865 eq9801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9801 eq31865
  have eq31929 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31906 eq1407
    | exact resolve eq1407 eq31906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31906
  have eq31942 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq31929
  have eq31952 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq31942
       have r₂ := eq3269
       grind)
    | exact resolve eq31942 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269 eq31942
  have eq31995 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq31952
       grind)
    | exact superpose eq31952 eq13
    | (have r₁ := eq13 X0 y
       have r₂ := eq31952
       grind)
    | exact resolve eq13 eq31952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32027 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1422 X0 y x
       have i₂ := eq31952
       grind)
    | exact superpose eq31952 eq1422
    | exact resolve eq1422 eq31952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32061 : (M.op y y) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7330 y y
       have i₂ := eq31952
       grind)
    | exact superpose eq31952 eq7330
    | exact resolve eq7330 eq31952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7330
  have eq32062 : (M.op y y) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq32061
  have eq32082 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31995
  have eq32103 : y = (M.op (σ x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31952 eq32062
    | exact resolve eq32062 eq31952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31952 eq32062
  have eq32151 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13054
       have i₂ := eq32082 sF0
       grind)
    | exact superpose eq32082 eq13054
    | exact resolve eq13054 eq32082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13054
  have eq32152 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq32082 sF0
       grind)
    | exact superpose eq32082 eq37
    | exact resolve eq37 eq32082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32082
  have eq32156 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq32151
  have eq32169 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32152
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32152
    | exact resolve eq32152 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32152
  have eq32175 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13068 eq32169
    | exact resolve eq32169 eq13068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13068 eq32169
  have eq32178 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq32156
       grind)
    | exact superpose eq32156 eq24
    | exact resolve eq24 eq32156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32275 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq32178
    | exact resolve eq32178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32178
  have eq32537 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32275 eq6042
    | (have r₁ := eq6042
       have r₂ := eq32275
       grind)
    | exact resolve eq6042 eq32275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6042 eq32275
  have eq32586 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32537
  have eq32587 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32586
  have eq32615 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3241 eq32587
    | exact resolve eq32587 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241 eq32587
  have eq32616 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32615
  have eq32638 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32616 eq27
    | exact resolve eq27 eq32616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32639 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32616 eq175
    | exact resolve eq175 eq32616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq32660 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32639 x
       have i₂ := eq542 sF2 x
       grind)
    | exact superpose eq542 eq32639
    | exact resolve eq32639 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32639
  have eq32698 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32660 eq1422
    | exact resolve eq1422 eq32660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32660
  have eq32804 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) X1)) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq32698 eq560
    | exact resolve eq560 eq32698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32828 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq32698 eq1578
    | exact resolve eq1578 eq32698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32848 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq32698 eq177
    | exact resolve eq177 eq32698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32698
  have eq33011 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) X1)) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq32848 eq32804
    | exact resolve eq32804 eq32848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32804
  have eq34644 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq33011
    | (have j0 := eq33011 (σ y)
       grind)
    | exact resolve eq33011 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33011
  have eq34793 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32616 eq34644
    | exact resolve eq34644 eq32616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32616 eq34644
  have eq34826 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34793 eq32828
    | exact resolve eq32828 eq34793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32828
  have eq34843 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 X0) X1)) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq34793 eq560
    | exact resolve eq560 eq34793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq34867 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq34793 eq1578
    | exact resolve eq1578 eq34793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34793
  have eq34916 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34826
  have eq34953 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) X1)) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq32848 eq34843
    | exact resolve eq34843 eq32848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32848 eq34843
  have eq35011 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (σ x) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34916 eq13
    | exact resolve eq13 eq34916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35067 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ (σ x) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34916 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq34916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35247 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34916 eq35067
    | (have j0 := eq35067 X0
       grind)
    | exact resolve eq35067 eq34916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35067
  have eq35257 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ (σ x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq35247 X0
       have j1 := eq35011 X0
       grind)
    | (have r₁ := eq35247 (σ y)
       have r₂ := eq35011 X0
       grind)
    | (have r₁ := eq35247 X0
       have r₂ := eq35011 X0
       grind)
    | exact resolve eq35247 eq35011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35011 eq35247
  have eq37905 : y = (M.op (σ y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32103 eq34953
    | exact resolve eq34953 eq32103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32103 eq34953
  have eq37941 : y = (M.op (σ y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq37905
  have eq37950 : x = (M.op (σ y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32156 eq37941
    | exact resolve eq37941 eq32156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37941
  have eq37954 : x = (M.op (σ x) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32175 eq37950
    | exact resolve eq37950 eq32175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32175 eq37950
  have eq38947 : (τ (σ x)) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35257 eq132
    | (have j1 := eq35257 (σ (M.op x y))
       grind)
    | exact resolve eq132 eq35257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq35257
  have eq38969 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38947
       have r₂ := eq32638
       grind)
    | exact resolve eq38947 eq32638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38947
  have eq38981 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq38969
    | exact resolve eq38969 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq38969
  have eq47602 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq32027 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq32027 x X0
       grind)
    | exact superpose eq32027 eq18
    | (have j1 := eq32027 X0 x
       grind)
    | exact resolve eq18 eq32027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32027
  have eq47883 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32156 eq47602
    | exact resolve eq47602 eq32156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32156 eq47602
  have eq48754 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37954
       have i₂ := eq47883 sF2
       grind)
    | exact superpose eq47883 eq37954
    | exact resolve eq37954 eq47883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37954 eq47883
  have eq48798 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq48754
  have eq48991 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38981
       have i₂ := eq48798
       grind)
    | exact superpose eq48798 eq38981
    | exact resolve eq38981 eq48798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38981
  have eq48992 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq48991
  have eq51012 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34867 eq6153
    | exact resolve eq6153 eq34867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34867
  have eq51024 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34916 eq51012
    | exact resolve eq51012 eq34916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34916 eq51012
  have eq52127 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51024 eq1407
    | exact resolve eq1407 eq51024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq51024
  have eq52142 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq52127
  have eq52156 : x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq52142
       have r₂ := eq32638
       grind)
    | exact resolve eq52142 eq32638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32638 eq52142
  have eq52165 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48798 eq52156
    | exact resolve eq52156 eq48798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48798 eq52156
  have eq52200 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52165 eq13
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq52165
       grind)
    | exact resolve eq13 eq52165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52165
  have eq52297 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq52200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52200
  have eq52372 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52297 eq48992
    | exact resolve eq48992 eq52297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48992 eq52297
  have eq52381 : x = (M.op x y) := by grind
  clear eq52372
  have eq52398 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq52381
       grind)
    | exact superpose eq52381 eq18
    | exact resolve eq18 eq52381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52399 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq52381
       grind)
    | exact superpose eq52381 eq22
    | exact resolve eq22 eq52381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq52402 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq52381
       grind)
    | exact superpose eq52381 eq174
    | exact resolve eq174 eq52381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq52381
  have eq52422 : (M.op x y) = (M.op (σ x) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq52402 x
       have i₂ := eq542 sF0 x
       grind)
    | exact superpose eq542 eq52402
    | exact resolve eq52402 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq52402
  have eq52424 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq52399 eq20
    | exact resolve eq20 eq52399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52399
  have eq52691 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq52422 eq1422
    | exact resolve eq1422 eq52422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52697 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq52422 eq1578
    | exact resolve eq1578 eq52422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578 eq52422
  have eq52809 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq52691 eq1422
    | exact resolve eq1422 eq52691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq52828 : (M.op x y) = (k (M.op x y) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op x y))) := by
    first
    | exact superpose eq52691 eq6153
    | exact resolve eq6153 eq52691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6153
  have eq52840 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op x y) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52691 eq16
    | exact resolve eq16 eq52691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52841 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq52691 eq177
    | exact resolve eq177 eq52691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq52691
  have eq52939 : ∀ X1 : G, (M.op (M.op x y) (M.op (M.op x y) X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq52840 X1 X1
       have i₂ := eq52841 (M.op sF0 X1) X1
       grind)
    | exact superpose eq52841 eq52840
    | exact resolve eq52840 eq52841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52840 eq52841
  have eq52942 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq52697 eq52828
    | exact resolve eq52828 eq52697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52697 eq52828
  have eq54272 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq52398 eq52939
    | exact resolve eq52939 eq52398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52398 eq52939
  have eq54412 : ∀ X0 : G, y = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq54272 eq52809
    | exact resolve eq52809 eq54272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52809 eq54272
  have eq55083 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq52942 eq37
    | exact resolve eq37 eq52942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq52942
  have eq55088 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq54412 eq55083
    | exact resolve eq55083 eq54412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54412 eq55083
  have eq55093 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq55088
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55088
    | exact resolve eq55088 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq55088
  have eq55095 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq52424 eq55093
    | exact resolve eq55093 eq52424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55093
  have eq55097 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq55095
    | exact resolve eq55095 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55095
  have eq55098 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq52424 eq55097
    | exact resolve eq55097 eq52424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55097
  have eq55108 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq55098 eq976
    | exact resolve eq976 eq55098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq55119 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55108
  have eq59511 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq55119 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq55119
       grind)
    | exact resolve eq13 eq55119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55119
  have eq59606 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq59511 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59511
  have eq59909 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq59606 eq55098
    | exact resolve eq55098 eq59606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59606
  have eq59955 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq59909 eq27
    | exact resolve eq27 eq59909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59909
  have eq59986 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq59955
       have r₂ := eq52424
       grind)
    | exact resolve eq59955 eq52424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59955
  have eq59996 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59986 eq26
    | exact resolve eq26 eq59986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq60116 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq59986 eq55098
    | exact resolve eq55098 eq59986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55098 eq59986
  have eq60340 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59996 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq59996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59996
  have eq60358 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60340
  have eq60363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60116 eq60358
    | exact resolve eq60358 eq60116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60116 eq60358
  have eq60364 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60363
  have eq60410 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq60364 eq27
    | exact resolve eq27 eq60364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60364
  have eq60440 : False := by grind
  exact eq60440

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_x_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq107 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq96
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq129
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq146
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq189 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq204 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq206 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X2) X3 X1
       have i₂ := eq53 X1 X0 X2
       grind)
    | (have i₁ := eq53 (M.op X1 X1) X1 X0
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq53 X2 X2 X2
       have i₂ := eq53 X2 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq53 X0 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq209 sF2
       have i₂ := eq53 sF2 x sF2
       grind)
    | (have i₁ := eq209 x
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq209
    | exact resolve eq209 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq354 sF4
       have i₂ := eq53 sF4 x sF2
       grind)
    | exact superpose eq53 eq354
    | exact resolve eq354 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq342 X3 X1 x
       have i₂ := eq342 X0 X1 x
       grind)
    | (have i₁ := eq342 X0 X1 X3
       have i₂ := eq342 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq14
    | exact resolve eq14 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq50
    | exact resolve eq50 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1113 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq51
    | exact resolve eq51 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1119 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq209
    | exact resolve eq209 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1084 X0 X1 x X3
       have i₂ := eq52 X0 x X1
       grind)
    | exact superpose eq52 eq1084
    | exact resolve eq1084 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1084
  have eq1186 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq834 eq53
    | exact resolve eq53 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq834
  have eq1190 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1186 X0 x
       have i₂ := eq357 X0 sF4 x
       grind)
    | exact superpose eq357 eq1186
    | exact resolve eq1186 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1198 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1190 sF4
       have i₂ := eq356 sF4 x sF4
       grind)
    | (have i₁ := eq1190 sF4
       have i₂ := eq356 sF4 sF4 x
       grind)
    | exact superpose eq356 eq1190
    | exact resolve eq1190 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq1190
  have eq3480 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq354 eq345
    | exact resolve eq345 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq354
  have eq3697 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq209 eq3480
    | exact resolve eq3480 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq3480
  have eq4650 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167
    | (have j0 := eq167 x
       grind)
    | exact resolve eq167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq4661 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4650
  have eq4665 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4661
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4661
    | exact resolve eq4661 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4661
  have eq4681 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4665
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq4665 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665
  have eq4687 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4681 eq49
    | exact resolve eq49 eq4681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq4900 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq4910 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4900
  have eq4913 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4910
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq4910
    | exact resolve eq4910 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4910
  have eq4936 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4913
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4913 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913
  have eq4951 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4936 eq84
    | exact resolve eq84 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5148 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq204
    | (have j0 := eq204 (M.op x y)
       grind)
    | exact resolve eq204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq5157 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5148
  have eq5159 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129 eq5157
    | exact resolve eq5157 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5157
  have eq5189 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5159
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq5159 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5159
  have eq5214 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5189 eq152
    | exact resolve eq152 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq12638 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4936 eq106
    | exact resolve eq106 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq12702 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4681 eq107
    | exact resolve eq107 eq4681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq4681
  have eq13711 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5189 eq153
    | exact resolve eq153 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq17551 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq12638
       grind)
    | exact superpose eq12638 eq16
    | exact resolve eq16 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12638
  have eq17604 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4951 eq17551
    | exact resolve eq17551 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17551
  have eq17607 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17604
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17604 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17604
  have eq17610 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq12702
       grind)
    | exact superpose eq12702 eq16
    | exact resolve eq16 eq12702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12702
  have eq17663 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4687 eq17610
    | exact resolve eq17610 eq4687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17610
  have eq17666 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq17663
       have r₂ := eq13 x x
       grind)
    | exact resolve eq17663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17663
  have eq17667 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq17607
       grind)
    | exact superpose eq17607 eq70
    | exact resolve eq70 eq17607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq17706 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4936 eq17667
    | exact resolve eq17667 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936 eq17667
  have eq18410 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13711 eq16
    | exact resolve eq16 eq13711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13711
  have eq18469 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5214 eq18410
    | exact resolve eq18410 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214 eq18410
  have eq18472 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq18469
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq18469 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18469
  have eq18473 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq18472 eq129
    | exact resolve eq129 eq18472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq18472
  have eq18512 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5189 eq18473
    | exact resolve eq18473 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5189 eq18473
  have eq24433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq24434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24433
    | exact resolve eq24433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24433
  have eq24445 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24434
       have r₂ := eq27
       grind)
    | exact resolve eq24434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24434
  have eq24449 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq24445 eq4951
    | exact resolve eq4951 eq24445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24445
  have eq24531 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24449
       have i₂ := eq17607
       grind)
    | exact superpose eq17607 eq24449
    | exact resolve eq24449 eq17607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24449
  have eq24540 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq24531
    | exact resolve eq24531 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24531
  have eq24541 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24540
  have eq24544 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq24541 eq14
    | exact resolve eq14 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24627 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24544 eq1113
    | exact resolve eq1113 eq24544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq24630 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24544 eq1119
    | exact resolve eq1119 eq24544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq24673 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq24544 eq1073
    | exact resolve eq1073 eq24544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24544
  have eq24936 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24630 eq24627
    | exact resolve eq24627 eq24630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24627 eq24630
  have eq24951 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24936
  have eq25792 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq24673
    | (have j0 := eq24673 (σ x) X0
       grind)
    | exact resolve eq24673 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24673
  have eq27290 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24541 eq24951
    | exact resolve eq24951 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24541 eq24951
  have eq27305 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq27290
  have eq27328 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27305 eq25792
    | exact resolve eq25792 eq27305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25792 eq27305
  have eq27400 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq27328
  have eq27444 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17706
       have i₂ := eq27400
       grind)
    | exact superpose eq27400 eq17706
    | exact resolve eq17706 eq27400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27478 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 y x
       have i₂ := eq27400
       grind)
    | exact superpose eq27400 eq1073
    | exact resolve eq1073 eq27400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27400
  have eq27515 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27444
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27444
    | exact resolve eq27444 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27444
  have eq27577 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq27515 eq1073
    | exact resolve eq1073 eq27515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27515
  have eq28552 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27478 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27478
    | (have j0 := eq27478 x X0
       grind)
    | exact resolve eq27478 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27478
  have eq28956 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17706
       have i₂ := eq28552 y
       grind)
    | exact superpose eq28552 eq17706
    | exact resolve eq17706 eq28552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28552
  have eq28984 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq28956
    | exact resolve eq28956 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28956
  have eq30276 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq27577
    | (have j0 := eq27577 (σ x) X0
       grind)
    | exact resolve eq27577 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27577
  have eq30807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30276 eq28984
    | exact resolve eq28984 eq30276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28984 eq30276
  have eq30810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq30807
  have eq30840 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30810
       have r₂ := eq27
       grind)
    | exact resolve eq30810 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30810
  have eq30852 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq30840
       grind)
    | exact superpose eq30840 eq14
    | exact resolve eq14 eq30840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30840
  have eq30922 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq30852 x
       have i₂ := eq342 X0 y x
       grind)
    | (have i₁ := eq30852 X0
       have i₂ := eq342 (M.op X0 X0) y x
       grind)
    | exact superpose eq342 eq30852
    | exact resolve eq30852 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq31021 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 (M.op y y) x
       have i₂ := eq30852 y
       grind)
    | exact superpose eq30852 eq1073
    | exact resolve eq1073 eq30852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30852
  have eq31615 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq31021 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31021
    | (have j0 := eq31021 x X0
       grind)
    | exact resolve eq31021 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31021
  have eq32082 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17706
       have i₂ := eq31615 y
       grind)
    | exact superpose eq31615 eq17706
    | exact resolve eq17706 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17706
  have eq32091 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq30922 X0
       have i₂ := eq31615 y
       grind)
    | exact superpose eq31615 eq30922
    | exact resolve eq30922 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30922 eq31615
  have eq32100 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq32091 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32091
  have eq32119 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq32082
    | exact resolve eq32082 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32082
  have eq32259 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32100 eq18512
    | exact resolve eq18512 eq32100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18512 eq32100
  have eq32276 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32259
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32259
    | exact resolve eq32259 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq32259
  have eq32372 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq32119 eq1169
    | exact resolve eq1169 eq32119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq32119
  have eq37981 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32276 eq32372
    | exact resolve eq32372 eq32276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32276 eq32372
  have eq38177 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37981 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37981
  have eq38343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38177 eq26
    | (have j1 := eq38177 (σ x)
       grind)
    | exact resolve eq26 eq38177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38177
  have eq38387 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq38343
       have r₂ := eq27
       grind)
    | exact resolve eq38343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38343
  have eq38401 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq38387 eq27
    | exact resolve eq27 eq38387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38412 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq38387 eq1198
    | exact resolve eq1198 eq38387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq38415 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ x)) X1)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq38387 eq3697
    | exact resolve eq3697 eq38387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq38426 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq38415 x X1
       have i₂ := eq357 sF2 X1 x
       grind)
    | exact superpose eq357 eq38415
    | exact resolve eq38415 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq38415
  have eq38427 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq378 eq38412
    | (have j0 := eq38412 (σ y)
       grind)
    | exact resolve eq38412 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq38412
  have eq38433 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq38387 eq38427
    | exact resolve eq38427 eq38387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38427
  have eq38468 : ∀ X0 : G, (k x x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq38426 eq4687
    | exact resolve eq4687 eq38426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4687 eq38426
  have eq38690 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq38468 X0
       have i₂ := eq17666
       grind)
    | exact superpose eq17666 eq38468
    | exact resolve eq38468 eq17666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17666 eq38468
  have eq38712 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq38433
       have i₂ := eq1073 sF2 sF2 x
       grind)
    | (have i₁ := eq38433
       have i₂ := eq1073 X0 sF2 sF2
       grind)
    | exact superpose eq1073 eq38433
    | exact resolve eq38433 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq38720 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq38433 eq1111
    | exact resolve eq1111 eq38433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq38721 : x = (M.op (σ x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq38433 eq1112
    | exact resolve eq1112 eq38433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq38433
  have eq43087 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq38712 eq38720
    | exact resolve eq38720 eq38712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43460 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq43087
    | (have j0 := eq43087 (σ y)
       grind)
    | exact resolve eq43087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq43557 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq38387 eq43460
    | exact resolve eq43460 eq38387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38387 eq43460
  have eq43968 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq43557 eq38712
    | exact resolve eq38712 eq43557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38712
  have eq43978 : (τ (σ y)) = (M.op x x) := by
    first
    | exact superpose eq43557 eq38690
    | exact resolve eq38690 eq43557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38690 eq43557
  have eq44077 : y = (M.op x x) := by
    first
    | exact superpose eq29 eq43978
    | exact resolve eq43978 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq43978
  have eq44825 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq43968 eq4951
    | exact resolve eq4951 eq43968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951 eq43968
  have eq44857 : (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq44825
       have i₂ := eq17607
       grind)
    | exact superpose eq17607 eq44825
    | exact resolve eq44825 eq17607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17607 eq44825
  have eq44889 : x = (M.op y y) := by
    first
    | exact superpose eq28 eq44857
    | exact resolve eq44857 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq44857
  have eq45764 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq206 y
       have i₂ := eq44889
       grind)
    | exact superpose eq44889 eq206
    | exact resolve eq206 eq44889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq45843 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq38720 y y
       have i₂ := eq44889
       grind)
    | exact superpose eq44889 eq38720
    | exact resolve eq38720 eq44889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38720 eq44889
  have eq45845 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq45843
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45843
    | exact resolve eq45843 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45843
  have eq45889 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq45764
       have i₂ := eq44077
       grind)
    | exact superpose eq44077 eq45764
    | exact resolve eq45764 eq44077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44077 eq45764
  have eq45922 : (M.op x y) = (M.op (σ x) y) := by
    first
    | exact superpose eq45845 eq43087
    | exact resolve eq43087 eq45845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43087 eq45845
  have eq45989 : x = (M.op (σ x) y) := by
    first
    | exact superpose eq45889 eq38721
    | exact resolve eq38721 eq45889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38721 eq45889
  have eq46220 : x = (M.op x y) := by
    first
    | exact superpose eq45922 eq45989
    | exact resolve eq45989 eq45922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45922 eq45989
  have eq46221 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq46220 eq20
    | exact resolve eq20 eq46220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46220
  have eq46434 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq46221
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46221
    | exact resolve eq46221 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq46221
  have eq46494 : False := by grind
  exact eq46494

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq85 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq86 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16797
    | exact resolve eq16797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16797
  have eq16809 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq16798
       have r₂ := eq28
       grind)
    | exact resolve eq16798 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16813 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16809
    | exact resolve eq16809 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16809
  have eq16818 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16813 eq86
    | (have r₁ := eq86
       have r₂ := eq16813
       grind)
    | exact resolve eq86 eq16813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq16813
  have eq16923 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq16818
  have eq16924 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq16923
  have eq16932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16924 eq77
    | exact resolve eq77 eq16924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq16924
  have eq16944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16932
  have eq16947 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16944
       have r₂ := eq28
       grind)
    | exact resolve eq16944 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16944
  have eq17074 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq16947
       grind)
    | exact superpose eq16947 eq52
    | exact resolve eq52 eq16947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq17076 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq16947
       grind)
    | exact superpose eq16947 eq85
    | (have r₁ := eq85
       have r₂ := eq16947
       grind)
    | exact resolve eq85 eq16947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq16947
  have eq17180 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq17076
  have eq17181 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17180
  have eq17214 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17074
    | exact resolve eq17074 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17074
  have eq17224 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq17181
       grind)
    | exact superpose eq17181 eq49
    | exact resolve eq49 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq17181
  have eq17246 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17224
    | exact resolve eq17224 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17224
  have eq17554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17246 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17246
  have eq17555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17554
  have eq17559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17555
    | exact resolve eq17555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17555
  have eq17570 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17559
       have r₂ := eq28
       grind)
    | exact resolve eq17559 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17559
  have eq17574 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17570
    | exact resolve eq17570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17570
  have eq17587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17574 eq17214
    | exact resolve eq17214 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17214 eq17574
  have eq17686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17587
  have eq17692 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17686
       have r₂ := eq28
       grind)
    | exact resolve eq17686 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17686
  have eq17820 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17692 eq30
    | exact resolve eq30 eq17692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17692
  have eq17926 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq17820
    | exact resolve eq17820 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17820
  have eq17927 : x = y := by grind
  clear eq17926
  have eq17946 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17927
       grind)
    | exact superpose eq17927 eq19
    | exact resolve eq19 eq17927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17947 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17927
       grind)
    | exact superpose eq17927 eq25
    | exact resolve eq25 eq17927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17927
  have eq18048 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17947
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17947
    | exact resolve eq17947 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17947
  have eq18063 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18048 eq27
    | exact resolve eq27 eq18048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18048
  have eq18363 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18063 eq68
    | exact resolve eq68 eq18063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq18063
  have eq18479 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18363
       have i₂ := eq17946
       grind)
    | exact superpose eq17946 eq18363
    | exact resolve eq18363 eq17946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17946 eq18363
  have eq18488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18479 eq15
    | exact resolve eq15 eq18479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18479
  have eq18534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18488
    | exact resolve eq18488 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18488
  have eq18543 : False := by grind
  exact eq18543

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq15
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq37
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq118 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1896 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq118 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1899 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1896 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1896 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1896 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq1896 X0 X1
       have r₂ := eq14 (M.op X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq1896 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq1932 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq1899 X0 (τ X1)
       grind)
    | exact superpose eq1899 eq29
    | (have j1 := eq1899 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq29 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1933 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1899 (σ X0) (σ X1)
       grind)
    | exact superpose eq1899 eq15
    | (have j1 := eq1899 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899
  have eq65327 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1932 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1932
    | exact resolve eq1932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq65442 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65327 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq65327
    | (have j0 := eq65327 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq65327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65327
  have eq241003 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1933 x y
       grind)
    | exact superpose eq1933 eq16
    | (have j1 := eq1933 x y
       grind)
    | exact resolve eq16 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq241210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq241003
       have i₂ := eq65442 y x
       grind)
    | exact superpose eq65442 eq241003
    | (have j1 := eq65442 (σ x) (σ y)
       grind)
    | (have r₁ := eq241003
       have r₂ := eq65442 y x
       grind)
    | (have r₁ := eq241003
       have r₂ := eq65442 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq241003
       have r₂ := eq65442 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq241003 eq65442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65442 eq241003
  have eq241211 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq241210
  have eq245317 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq241211
       grind)
    | exact superpose eq241211 eq10
    | exact resolve eq10 eq241211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241211
  have eq245386 : x = y ∨ x = y := by
    first
    | (have i₁ := eq245317
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq245317
    | exact resolve eq245317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245317
  have eq245387 : x = y := by grind
  clear eq245386
  have eq249683 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq245387
       grind)
    | exact superpose eq245387 eq16
    | exact resolve eq16 eq245387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245387
  have eq249684 : False := by grind
  exact eq249684

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  clear eq49
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq86 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq241 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq230 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq230
    | exact resolve eq230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq242 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq241
  have eq375 : ∀ X0 : G, (σ x) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq214 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq214
    | exact resolve eq214 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq494 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq650 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq242 X0
       grind)
    | exact superpose eq242 eq16
    | exact resolve eq16 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq864 : ∀ X0 : G, x = (M.op (τ (M.op X0 X0)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq53
    | exact resolve eq53 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq869 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (τ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq211 (τ X0)
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq211
    | exact resolve eq211 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (τ (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq214 (τ X0)
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq214
    | exact resolve eq214 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq1252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1252
    | exact resolve eq1252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1256 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1253
       have r₂ := eq28
       grind)
    | exact resolve eq1253 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1258 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1256
    | exact resolve eq1256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1261 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1258 eq54
    | exact resolve eq54 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1262 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1258 eq86
    | (have r₁ := eq86
       have r₂ := eq1258
       grind)
    | exact resolve eq86 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1266 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1262
  have eq1267 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1266
  have eq1334 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1267 eq77
    | exact resolve eq77 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1267
  have eq1338 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1334
  have eq1507 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1261 eq14
    | exact resolve eq14 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1526 : x = (M.op (τ (σ x)) (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1261 eq864
    | exact resolve eq864 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq1528 : (M.op (M.op x y) x) = (M.op (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1261 eq869
    | exact resolve eq869 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1529 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (τ (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1261 eq870
    | exact resolve eq870 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1538 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op x (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1529
    | exact resolve eq1529 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1539 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1528
    | exact resolve eq1528 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1541 : x = (M.op x (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1526
    | exact resolve eq1526 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1593 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq494 X3 X1 x
       have i₂ := eq494 X0 X1 x
       grind)
    | (have i₁ := eq494 X0 X1 X3
       have i₂ := eq494 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1595 : ∀ X1 : G, (σ x) = (M.op X1 (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq1261 eq494
    | exact resolve eq494 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1606 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1608 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X1 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1261 eq494
    | exact resolve eq494 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1640 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq494 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq494 eq14
    | exact resolve eq14 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq1721 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X1 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq214 eq1608
    | exact resolve eq1608 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq1608
  have eq1722 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1606 X0 X1 x X3
       have i₂ := eq55 X0 x X1
       grind)
    | exact superpose eq55 eq1606
    | exact resolve eq1606 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1606
  have eq1801 : x = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1539 eq1541
    | exact resolve eq1541 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539 eq1541
  have eq1811 : x = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1801
  have eq1953 : ∀ X0 : G, (M.op x (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1721 eq1538
    | exact resolve eq1538 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq1721
  have eq1982 : ∀ X0 : G, (M.op x (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq2630 : (σ (M.op x y)) = (M.op x (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1982 eq1338
    | exact resolve eq1338 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq2643 : (σ (M.op x y)) = (M.op x (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2630
  have eq2663 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2643 eq1982
    | exact resolve eq1982 eq2643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq2643
  have eq2677 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2830 : (τ (σ (M.op x y))) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2677 eq68
    | exact resolve eq68 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2867 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2830
    | exact resolve eq2830 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2830
  have eq3045 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1811
       have i₂ := eq2867
       grind)
    | exact superpose eq2867 eq1811
    | exact resolve eq1811 eq2867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811 eq2867
  have eq3080 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3045
  have eq4550 : (M.op x y) = (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq513 eq512
    | exact resolve eq512 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq513
  have eq17697 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := hcon
    have f17697_18 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
      intro X0 X1
      grind
    have f17697_19 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
      intro X0
      grind
    have f17697_28 : X0 ≠ (M.op (σ x) (M.op (σ x) X0)) := by grind
    have f17697_32 : (σ x) ≠ (σ y) := by grind
    have f17697_33 : x ≠ (M.op x y) := by grind
    have f17697_34 : x ≠ y := by grind
    have f17697_36 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = y := by
      intro X0
      first
      | (have j0 := f17697_19 X0
         grind)
      | (have r₁ := f17697_19 X0
         have r₂ := f17697_32
         grind)
      | exact resolve f17697_19 f17697_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_37 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f17697_18 X0 X1
         grind)
      | (have r₁ := f17697_18 X0 X1
         have r₂ := f17697_32
         grind)
      | exact resolve f17697_18 f17697_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_38 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = y := by
      intro X0
      first
      | (have j0 := f17697_36 X0
         grind)
      | (have r₁ := f17697_36 X0
         have r₂ := f17697_33
         grind)
      | exact resolve f17697_36 f17697_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_39 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f17697_37 X0 X1
         grind)
      | (have r₁ := f17697_37 X0 X1
         have r₂ := f17697_33
         grind)
      | exact resolve f17697_37 f17697_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_40 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f17697_38 X0
         grind)
      | (have r₁ := f17697_38 X0
         have r₂ := f17697_34
         grind)
      | exact resolve f17697_38 f17697_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_41 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have j0 := f17697_39 X0 X1
         grind)
      | (have r₁ := f17697_39 X0 X1
         have r₂ := f17697_34
         grind)
      | exact resolve f17697_39 f17697_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_48 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
      intro X0
      first
      | (have i₁ := f17697_41 X0 (M.op (σ x) (σ x))
         have i₂ := f17697_40 X0
         grind)
      | exact superpose f17697_40 f17697_41
      | exact resolve f17697_41 f17697_40
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_61 : X0 ≠ X0 := by
      first
      | (have i₁ := f17697_28
         have i₂ := f17697_48 X0
         grind)
      | exact superpose f17697_48 f17697_28
      | (have r₁ := f17697_28
         have r₂ := f17697_48 X0
         grind)
      | exact resolve f17697_28 f17697_48
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17697_64 : False := by grind
    exact f17697_64
  clear eq1507 eq1595
  have eq18095 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq17697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17697
  have eq18208 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq18095
    | (have j0 := eq18095 (σ y)
       grind)
    | exact resolve eq18095 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18095
  have eq18310 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1258 eq18208
    | exact resolve eq18208 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq18208
  have eq18326 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18310
  have eq18428 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18326 eq2677
    | exact resolve eq2677 eq18326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677 eq18326
  have eq18508 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18428
  have eq18536 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18508 eq30
    | exact resolve eq30 eq18508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18508
  have eq18557 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18536
    | exact resolve eq18536 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18536
  have eq18558 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18557
  have eq18622 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18558 eq30
    | exact resolve eq30 eq18558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18558
  have eq18666 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq18622
    | exact resolve eq18622 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18622
  have eq18717 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18666 eq3080
    | exact resolve eq3080 eq18666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080 eq18666
  have eq18794 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18717
  have eq18807 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18794
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18794
    | exact resolve eq18794 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18794
  have eq18808 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18807
  have eq18848 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18808 eq30
    | exact resolve eq30 eq18808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18808
  have eq18871 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18848
    | exact resolve eq18848 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18848
  have eq18872 : x = (M.op x y) ∨ x = y := by grind
  clear eq18871
  have eq18949 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq18872 eq21
    | exact resolve eq21 eq18872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18987 : x = (M.op x (M.op (M.op x x) x)) ∨ x = y := by
    first
    | exact superpose eq18872 eq4550
    | exact resolve eq4550 eq18872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4550
  have eq18991 : x = (M.op x (M.op (M.op x y) x)) ∨ x = y := by
    first
    | (have i₁ := eq18987
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq18987
    | exact resolve eq18987 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq18987
  have eq19022 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq18949
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18949
    | exact resolve eq18949 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18949
  have eq19425 : x = (M.op x (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18872 eq18991
    | exact resolve eq18991 eq18872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18991
  have eq19455 : x = (M.op x (M.op x x)) ∨ x = y := by grind
  clear eq19425
  have eq20455 : ∀ X0 : G, x = (M.op X0 (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19455
       have i₂ := eq1593 x x X0
       grind)
    | (have i₁ := eq19455
       have i₂ := eq1593 X0 x x
       grind)
    | exact superpose eq1593 eq19455
    | exact resolve eq19455 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq20467 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1722 x x X0
       have i₂ := eq19455
       grind)
    | exact superpose eq19455 eq1722
    | exact resolve eq1722 eq19455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq21219 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq375 (M.op x x)
       have i₂ := eq20455 (M.op x x)
       grind)
    | exact superpose eq20455 eq375
    | exact resolve eq375 eq20455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq21225 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq383 (M.op x x)
       have i₂ := eq20455 (M.op x x)
       grind)
    | exact superpose eq20455 eq383
    | exact resolve eq383 eq20455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq21345 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq21225
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21225
    | exact resolve eq21225 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21225
  have eq21349 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq21219
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21219
    | exact resolve eq21219 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21219
  have eq21649 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52
       have i₂ := eq20467 X0
       grind)
    | (have i₁ := eq52
       have i₂ := eq20467 x
       grind)
    | exact superpose eq20467 eq52
    | exact resolve eq52 eq20467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq20467
  have eq23119 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21345 eq21349
    | exact resolve eq21349 eq21345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21345 eq21349
  have eq23155 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq23119
  have eq40757 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1640 x x X0 X1
       have i₂ := eq19455
       grind)
    | exact superpose eq19455 eq1640
    | exact resolve eq1640 eq19455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640 eq19455
  have eq46706 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40757 X0 (M.op x x)
       have i₂ := eq20455 X0
       grind)
    | exact superpose eq20455 eq40757
    | exact resolve eq40757 eq20455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20455 eq40757
  have eq47338 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq46706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46706
  have eq47383 : y = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq47338 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47338
    | (have j0 := eq47338 y
       grind)
    | exact resolve eq47338 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47338
  have eq47573 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18872 eq47383
    | exact resolve eq47383 eq18872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18872 eq47383
  have eq47616 : y = (M.op x x) ∨ x = y := by grind
  clear eq47573
  have eq47672 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq21649 x
       have i₂ := eq47616
       grind)
    | exact superpose eq47616 eq21649
    | exact resolve eq21649 eq47616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21649 eq47616
  have eq47772 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq47672
  have eq47835 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq47772
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq47772
    | exact resolve eq47772 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47772
  have eq48577 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq47835 eq23155
    | exact resolve eq23155 eq47835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23155 eq47835
  have eq48724 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq48577
  have eq48752 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq48724
    | exact resolve eq48724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48724
  have eq48756 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq48752 eq28
    | exact resolve eq28 eq48752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48752
  have eq48797 : x = y := by
    first
    | (have r₁ := eq48756
       have r₂ := eq19022
       grind)
    | exact resolve eq48756 eq19022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19022 eq48756
  have eq48798 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq48797
       grind)
    | exact superpose eq48797 eq19
    | exact resolve eq19 eq48797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq48799 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq48797
       grind)
    | exact superpose eq48797 eq25
    | exact resolve eq25 eq48797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq48797
  have eq48920 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq48799
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48799
    | exact resolve eq48799 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq48799
  have eq48940 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq48920 eq27
    | exact resolve eq27 eq48920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq48920
  have eq49210 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq48940 eq68
    | exact resolve eq68 eq48940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq48940
  have eq49339 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq49210
       have i₂ := eq48798
       grind)
    | exact superpose eq48798 eq49210
    | exact resolve eq49210 eq48798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48798 eq49210
  have eq49344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49339 eq15
    | exact resolve eq15 eq49339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49339
  have eq49420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq49344
    | exact resolve eq49344 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq49344
  have eq49441 : False := by grind
  exact eq49441

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 (M.op X1 X0) X1
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
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
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (k X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq179
    | exact resolve eq179 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq182 : ∀ X0 : G, (σ x) = (M.op (k X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 : G, x = (M.op (k X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq176
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq185 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ x) = (M.op (σ (k X0 X0)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq182 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, x = (M.op (σ (k X0 X0)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq183 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq183
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq439 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq317 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq317
    | exact resolve eq317 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq577 : ∀ X0 : G, x = (M.op (τ (k X0 X0)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq183 (τ X0)
       have i₂ := eq439 X0 X0
       grind)
    | exact superpose eq439 eq183
    | exact resolve eq183 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (M.op (k X1 X1) (k X0 X0)) = (M.op x (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq183 eq180
    | exact resolve eq180 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq647 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (k X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq180 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 x X0 y
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ x) X0 (σ y)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 X3 : G, (M.op (k X0 X0) X1) = (M.op (k X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq180 X1 X3 x
       have i₂ := eq180 X1 X0 x
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (k X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 x
       have i₂ := eq180 X1 X0 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq182 x
       have i₂ := eq180 (M.op sF4 sF2) x x
       grind)
    | exact superpose eq180 eq182
    | exact resolve eq182 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 X2 : G, (M.op (k X2 X2) (M.op (k X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq656 X0 X1 X2
       have i₂ := eq175 X2
       grind)
    | exact superpose eq175 eq656
    | exact resolve eq656 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq667 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (σ (k X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq647 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq647
    | exact resolve eq647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (τ (k X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq647 (τ X0)
       have i₂ := eq439 X0 X0
       grind)
    | exact superpose eq439 eq647
    | exact resolve eq647 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq670 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq180 x x X0
       have i₂ := eq647 x
       grind)
    | exact superpose eq647 eq180
    | exact resolve eq180 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq674 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (k X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq648 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq648
    | exact resolve eq648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : (M.op x y) = (k x y) ∨ y = (M.op y x) := by
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
  have eq877 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq946 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq872
       grind)
    | exact superpose eq872 eq41
    | exact resolve eq41 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq947 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
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
  have eq949 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq947
    | exact resolve eq947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq949 eq877
    | exact resolve eq877 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq949
  have eq964 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq957
       have r₂ := eq27
       grind)
    | exact resolve eq957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq971 : ∀ X0 : G, (σ y) = (M.op (k X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq964 eq185
    | exact resolve eq185 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq964 eq180
    | exact resolve eq180 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq972 X0
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq972
    | exact resolve eq972 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq977 : ∀ X0 : G, (σ y) = (M.op (k X0 X0) (k (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq971 X0
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq971
    | exact resolve eq971 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq982 : (σ y) = (M.op x (k (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq977 x
       have i₂ := eq645 sF3 x
       grind)
    | exact superpose eq645 eq977
    | exact resolve eq977 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq986 : (M.op (M.op x y) x) = (M.op (σ y) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq982 eq670
    | exact resolve eq670 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1000 : ∀ X0 : G, (σ y) = (M.op (k X0 X0) (M.op (M.op (M.op x y) x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq986 eq185
    | exact resolve eq185 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 : G, (M.op (k X0 X0) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq986 eq180
    | exact resolve eq180 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1004 : (k (σ y) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq976 eq1001
    | exact resolve eq1001 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq1001
  have eq1442 : ∀ X0 : G, (σ y) = (M.op (σ (k X0 X0)) (M.op (M.op (M.op x y) x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1000 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1000
    | exact resolve eq1000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1472 : ∀ X0 : G, (σ y) = (M.op (σ (k X0 X0)) (k (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1004 eq1442
    | exact resolve eq1442 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004 eq1442
  have eq1562 : (σ y) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1472 y
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq1472
    | exact resolve eq1472 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1579 : (σ y) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1562
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1562
    | exact resolve eq1562 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1591 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1579
       have i₂ := eq175 (k sF3 sF3)
       grind)
    | exact superpose eq175 eq1579
    | exact resolve eq1579 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq1600 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1591 eq182
    | exact resolve eq182 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1610 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1591 eq648
    | exact resolve eq648 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq1635 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq964 eq1610
    | exact resolve eq1610 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq1610
  have eq1646 : ∀ X0 : G, (σ x) = (M.op (k X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1635 eq182
    | exact resolve eq182 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1667 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1600 eq180
    | exact resolve eq180 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1674 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq1667
    | (have j0 := eq1667 X0
       grind)
    | exact resolve eq1667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1683 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1646 eq1674
    | exact resolve eq1674 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646 eq1674
  have eq1693 : ∀ X0 : G, y = (M.op (k X0 X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq185 X0 y x
       have i₂ := eq1683
       grind)
    | exact superpose eq1683 eq185
    | exact resolve eq185 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1699 : ∀ X0 : G, y = (M.op (k X0 X0) (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1693 X0
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq1693
    | exact resolve eq1693 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1704 : y = (M.op x (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1699 x
       have i₂ := eq645 y x
       grind)
    | exact superpose eq645 eq1699
    | exact resolve eq1699 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq1885 : (M.op (M.op x y) x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq670 (k y y)
       have i₂ := eq1704
       grind)
    | exact superpose eq1704 eq670
    | exact resolve eq670 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq1889 : ∀ X0 : G, x = (M.op (k X0 X0) (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq185 X0 x (k y y)
       have i₂ := eq1704
       grind)
    | exact superpose eq1704 eq185
    | exact resolve eq185 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1894 : ∀ X0 : G, x = (M.op (k X0 X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1683 eq1889
    | exact resolve eq1889 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq1897 : y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1683 eq1885
    | exact resolve eq1885 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq2028 : ∀ X0 : G, x = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq180 y x X0
       have i₂ := eq1894 x
       grind)
    | exact superpose eq1894 eq180
    | exact resolve eq180 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2100 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2028 x
       have i₂ := eq1683
       grind)
    | exact superpose eq1683 eq2028
    | exact resolve eq2028 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683 eq2028
  have eq2114 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2100
  have eq2119 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2114
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq2114
    | exact resolve eq2114 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq2123 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1704
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq1704
    | exact resolve eq1704 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704
  have eq2125 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq41
    | exact resolve eq41 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2126 : (σ x) = (M.op x (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq182
    | exact resolve eq182 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2136 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op x (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq648 y
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq648
    | exact resolve eq648 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq2137 : (M.op (M.op x y) x) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq667 y
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq667
    | exact resolve eq667 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq2139 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq674 y
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq674
    | exact resolve eq674 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2148 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1894 y
       have i₂ := eq2119
       grind)
    | exact superpose eq2119 eq1894
    | exact resolve eq1894 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq2119
  have eq2149 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2148
  have eq2150 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2123
  have eq2151 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2149
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2149
    | exact resolve eq2149 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2152 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2139
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2139
    | exact resolve eq2139 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139
  have eq2154 : (M.op (M.op x y) x) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2137
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2137
    | exact resolve eq2137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137
  have eq2161 : (σ x) = (M.op x (M.op x (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2136 eq2126
    | exact resolve eq2126 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2162 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2125
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2125
    | exact resolve eq2125 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2164 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2150
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq2150
    | exact resolve eq2150 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2165 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2152
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq2152
    | exact resolve eq2152 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2167 : y = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1897 eq2154
    | exact resolve eq2154 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq2154
  have eq2174 : (σ x) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2151 eq2161
    | exact resolve eq2161 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2175 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2162
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2162
    | exact resolve eq2162 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2177 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2151 eq2164
    | exact resolve eq2164 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2178 : y = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2151 eq2167
    | exact resolve eq2167 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2297 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2177 eq188
    | exact resolve eq188 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq2305 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2177 eq674
    | exact resolve eq674 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq2318 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2305
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2305
    | exact resolve eq2305 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2326 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2297
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2297
    | exact resolve eq2297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq2332 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2165 eq2318
    | exact resolve eq2318 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2339 : (σ x) = (M.op (σ y) (M.op x (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2136 eq2326
    | exact resolve eq2326 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136 eq2326
  have eq2346 : (σ x) = (M.op (σ y) (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2151 eq2339
    | exact resolve eq2339 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq2630 : ∀ X0 : G, (σ x) = (M.op (k X0 X0) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2165 eq182
    | exact resolve eq182 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq2165
  have eq2649 : (σ x) = (M.op x (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2630 x
       have i₂ := eq645 sF2 x
       grind)
    | exact superpose eq645 eq2630
    | exact resolve eq2630 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq2630
  have eq2651 : (σ x) = (M.op (M.op x y) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2151 eq2649
    | exact resolve eq2649 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq2656 : ∀ X0 : G, (M.op x y) = (M.op (k X0 X0) (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2174 eq185
    | exact resolve eq185 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2661 : ∀ X0 : G, (M.op x y) = (M.op (k X0 X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2178 eq2656
    | exact resolve eq2656 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178 eq2656
  have eq2722 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2332 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq2332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2332
  have eq2727 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2722
    | exact resolve eq2722 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722
  have eq2728 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2727
  have eq2786 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2346 eq180
    | exact resolve eq180 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346
  have eq2789 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq2786
    | (have j0 := eq2786 X0
       grind)
    | exact resolve eq2786 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq2889 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2177 eq2661
    | exact resolve eq2661 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661
  have eq2911 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2889
  have eq2915 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2911
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq2911
    | exact resolve eq2911 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq3516 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq41
    | exact resolve eq41 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq3564 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3516
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3516
    | exact resolve eq3516 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3516
  have eq3577 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3564
    | exact resolve eq3564 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq3585 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2175 eq3577
    | exact resolve eq3577 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175 eq3577
  have eq3772 : (k y x) = (τ (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2728 eq115
    | exact resolve eq115 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq3780 : (k x x) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98 eq3772
    | exact resolve eq3772 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772
  have eq3783 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2151 eq3780
    | exact resolve eq3780 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151 eq3780
  have eq3786 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2177 eq3783
    | exact resolve eq3783 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177 eq3783
  have eq3790 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3786 eq42
    | exact resolve eq42 eq3786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq3786
  have eq3793 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3790
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3790
    | exact resolve eq3790 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3790
  have eq3795 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3585 eq3793
    | exact resolve eq3793 eq3585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585 eq3793
  have eq3799 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3795 eq2728
    | exact resolve eq2728 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728 eq3795
  have eq3805 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3799
  have eq3818 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3805 eq2651
    | exact resolve eq2651 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq3805
  have eq3856 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3818
  have eq3916 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2789 y
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq2789
    | exact resolve eq2789 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789 eq2915
  have eq3948 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3916
  have eq3956 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3856 eq3948
    | exact resolve eq3948 eq3856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3856 eq3948
  have eq3957 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3956
  have eq3965 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3957 eq27
    | exact resolve eq27 eq3957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq4387 : ∀ X0 X1 : G, (M.op (k X1 X1) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq659 eq180
    | exact resolve eq180 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq4394 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = (M.op (k X1 X1) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq3957 eq4387
    | exact resolve eq4387 eq3957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4387
  have eq4414 : ∀ X0 X1 : G, (M.op (σ x) (M.op (k (σ x) (σ x)) X0)) = (M.op (k X1 X1) (M.op (k (σ x) (σ x)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4394 X0 X1
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq4394
    | exact resolve eq4394 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4394
  have eq4429 : ∀ X0 : G, (M.op (σ x) (M.op (k (σ x) (σ x)) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4414 x x
       have i₂ := eq664 sF2 x x
       grind)
    | exact superpose eq664 eq4414
    | exact resolve eq4414 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq4414
  have eq4518 : ∀ X0 X1 : G, (M.op (σ x) (M.op (k X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4429 X1
       have i₂ := eq650 sF2 X1 x
       grind)
    | (have i₁ := eq4429 X1
       have i₂ := eq650 X0 X1 sF2
       grind)
    | exact superpose eq650 eq4429
    | exact resolve eq4429 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4520 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4429 (M.op (M.op X1 x) X1)
       have i₂ := eq185 sF2 X1 x
       grind)
    | exact superpose eq185 eq4429
    | exact resolve eq4429 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq4429
  have eq4726 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4518 x X0
       have i₂ := eq180 X0 x X1
       grind)
    | exact superpose eq180 eq4518
    | exact resolve eq4518 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq4771 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4726 X0 x
       have i₂ := eq4520 X0 x
       grind)
    | exact superpose eq4520 eq4726
    | exact resolve eq4726 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4520 eq4726
  have eq4785 : ∀ X0 X1 : G, (M.op (k X1 X1) X0) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | exact superpose eq4518 eq4771
    | exact resolve eq4771 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518
  have eq4792 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq4771
    | (have j0 := eq4771 (σ y)
       grind)
    | exact resolve eq4771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4817 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3957 eq4792
    | exact resolve eq4792 eq3957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4792
  have eq4822 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4817
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq4817
    | exact resolve eq4817 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817
  have eq4825 : (τ (σ y)) = (k x x) := by
    first
    | exact superpose eq4822 eq98
    | exact resolve eq98 eq4822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq4845 : x = (M.op (τ (σ y)) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq4822 eq577
    | exact resolve eq577 eq4822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq4850 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | exact superpose eq4822 eq650
    | exact resolve eq650 eq4822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq4822
  have eq4877 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq4850 x X1
       have i₂ := eq4785 X1 x
       grind)
    | exact superpose eq4785 eq4850
    | exact resolve eq4850 eq4785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4850
  have eq4881 : x = (M.op y (M.op (M.op x y) x)) := by
    first
    | exact superpose eq32 eq4845
    | exact resolve eq4845 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845
  have eq4889 : y = (k x x) := by
    first
    | exact superpose eq32 eq4825
    | exact resolve eq4825 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4825
  have eq5290 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq4877 eq175
    | exact resolve eq175 eq4877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq5308 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq5290
    | exact resolve eq5290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5290
  have eq5321 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq3957 eq5308
    | exact resolve eq5308 eq3957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957 eq5308
  have eq5328 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq5321 eq116
    | exact resolve eq116 eq5321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq5356 : (M.op (M.op x y) x) = (M.op (τ (σ x)) x) := by
    first
    | exact superpose eq5321 eq668
    | exact resolve eq668 eq5321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq5321
  have eq5377 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | exact superpose eq30 eq5356
    | exact resolve eq5356 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5356
  have eq5390 : x = (k y y) := by
    first
    | exact superpose eq30 eq5328
    | exact resolve eq5328 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5328
  have eq5391 : (k x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq5377
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq5377
    | exact resolve eq5377 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq5396 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq5391
       have i₂ := eq4889
       grind)
    | exact superpose eq4889 eq5391
    | exact resolve eq5391 eq4889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4889 eq5391
  have eq5410 : x = (M.op (σ x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq5390
       grind)
    | exact superpose eq5390 eq191
    | exact resolve eq191 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq5390
  have eq5455 : x = (M.op (σ x) y) := by
    first
    | exact superpose eq5396 eq5410
    | exact resolve eq5410 eq5396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5396 eq5410
  have eq5468 : x = (M.op (σ x) y) := by
    first
    | (have i₁ := eq5455
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5455
    | exact resolve eq5455 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5455
  have eq5624 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4881 eq16
    | exact resolve eq16 eq4881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4881
  have eq5635 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5624 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5624
    | (have j0 := eq5624 X0
       grind)
    | exact resolve eq5624 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5624
  have eq5639 : ∀ X0 : G, y = (M.op (k X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq5635 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq5635
    | exact resolve eq5635 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq5635
  have eq5640 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq5639 x
       have i₂ := eq4785 sF0 x
       grind)
    | exact superpose eq4785 eq5639
    | exact resolve eq5639 eq4785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785 eq5639
  have eq5642 : (M.op x y) = (M.op (σ x) y) := by
    first
    | exact superpose eq5640 eq4771
    | exact resolve eq4771 eq5640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4771 eq5640
  have eq5669 : x = (M.op x y) := by
    first
    | exact superpose eq5642 eq5468
    | exact resolve eq5468 eq5642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5468 eq5642
  have eq5698 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5669
       grind)
    | exact superpose eq5669 eq22
    | exact resolve eq22 eq5669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5669
  have eq5814 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5698 eq20
    | exact resolve eq20 eq5698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5698
  have eq5832 : False := by grind
  exact eq5832

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 (M.op y y) y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq92 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1433 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq487 X3 X1 x
       have i₂ := eq487 X0 X1 x
       grind)
    | (have i₁ := eq487 X0 X1 X3
       have i₂ := eq487 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq487 eq487
    | exact resolve eq487 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq12938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq76 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq12939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq12938
    | exact resolve eq12938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12938
  have eq12949 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq12939
       have r₂ := eq28
       grind)
    | exact resolve eq12939 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12939
  have eq12952 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq12949 eq124
    | exact resolve eq124 eq12949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq12949
  have eq13059 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq12952
    | exact resolve eq12952 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12952
  have eq13060 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13059
  have eq13063 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq13060
       grind)
    | exact superpose eq13060 eq93
    | exact resolve eq93 eq13060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13121 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1433 X0 y x
       have i₂ := eq13060
       grind)
    | exact superpose eq13060 eq1433
    | exact resolve eq1433 eq13060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13060
  have eq13179 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13063
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13063
    | exact resolve eq13063 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13063
  have eq13242 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq13179 eq1433
    | exact resolve eq1433 eq13179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq13179
  have eq13616 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13121 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13121
    | (have j0 := eq13121 x X0
       grind)
    | exact resolve eq13121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13121
  have eq14000 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq13616 y
       grind)
    | exact superpose eq13616 eq93
    | exact resolve eq93 eq13616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq13616
  have eq14025 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq14000
    | exact resolve eq14000 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14000
  have eq30445 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq13242
    | (have j0 := eq13242 (σ x) X0
       grind)
    | exact resolve eq13242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13242
  have eq31012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30445 eq14025
    | exact resolve eq14025 eq30445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14025 eq30445
  have eq31023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31012
  have eq31041 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq31023
       have r₂ := eq28
       grind)
    | exact resolve eq31023 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31023
  have eq31046 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31041 eq30
    | exact resolve eq30 eq31041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31041
  have eq31235 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq31046
    | exact resolve eq31046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31046
  have eq31236 : x = y := by grind
  clear eq31235
  have eq31252 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq31236
       grind)
    | exact superpose eq31236 eq19
    | exact resolve eq19 eq31236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq31253 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq31236
       grind)
    | exact superpose eq31236 eq25
    | exact resolve eq25 eq31236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq31236
  have eq31374 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31253
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31253
    | exact resolve eq31253 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31253
  have eq31394 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31374 eq27
    | exact resolve eq27 eq31374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq31374
  have eq31725 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31394 eq68
    | exact resolve eq68 eq31394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq31394
  have eq31833 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq31725
       have i₂ := eq31252
       grind)
    | exact superpose eq31252 eq31725
    | exact resolve eq31725 eq31252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31252 eq31725
  have eq31841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31833 eq15
    | exact resolve eq15 eq31833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31833
  have eq31917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq31841
    | exact resolve eq31841 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31841
  have eq31938 : False := by grind
  exact eq31938

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq208 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq812 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq851 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq812 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq812
    | (have j0 := eq812 X0 X1
       grind)
    | exact resolve eq812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq1278 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq208 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq208
    | (have j0 := eq208 (σ X0) (σ X1)
       grind)
    | exact resolve eq208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq4123 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 (σ X1) X1
       grind)
    | (have r₁ := eq13 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq84 (M.op (M.op (σ X1) (σ X1)) X1) X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4149 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq4150 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq4152 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4123 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4123
  have eq4153 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4152
  have eq4155 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4150 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4150
    | (have j0 := eq4150 X0
       grind)
    | exact resolve eq4150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4150
  have eq4204 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq4155 X0
       grind)
    | exact superpose eq4155 eq38
    | (have j1 := eq4155 X0
       grind)
    | exact resolve eq38 eq4155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4155
  have eq4225 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4204 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4204
    | (have j0 := eq4204 X0
       grind)
    | exact resolve eq4204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4226 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225
  have eq4229 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4226 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4226
    | exact resolve eq4226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4254 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4226 X0
       grind)
    | exact superpose eq4226 eq11
    | exact resolve eq11 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4316 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4229 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4229
    | exact resolve eq4229 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4472 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4316 X0
       grind)
    | exact superpose eq4316 eq11
    | exact resolve eq11 eq4316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316
  have eq4583 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4472 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4472
    | exact resolve eq4472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472
  have eq5237 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5275 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5237 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5237
    | exact resolve eq5237 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5237
  have eq5324 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5275 X0
       have i₂ := eq4583 X0
       grind)
    | exact superpose eq4583 eq5275
    | exact resolve eq5275 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275
  have eq5355 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5324
  have eq30368 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1278 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq1278
    | (have j0 := eq1278 (τ X0) (τ X1)
       grind)
    | exact resolve eq1278 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1278
  have eq30447 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30368 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq30368
    | (have j0 := eq30368 X0 X1
       grind)
    | exact resolve eq30368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30368
  have eq30503 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30447 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30447
    | (have j0 := eq30447 X0 X1
       grind)
    | exact resolve eq30447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30447
  have eq30558 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30503 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30503
    | (have j0 := eq30503 X0 X1
       grind)
    | exact resolve eq30503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30503
  have eq30610 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30558 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30558
    | (have j0 := eq30558 X0 X1
       grind)
    | exact resolve eq30558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30558
  have eq30653 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30610 X0 X1
       have i₂ := eq4254 (σ (τ X1))
       grind)
    | exact superpose eq4254 eq30610
    | (have j0 := eq30610 X0 X1
       grind)
    | exact resolve eq30610 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30610
  have eq30694 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30653 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq30653
    | (have j0 := eq30653 X0 X1
       grind)
    | exact resolve eq30653 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30653
  have eq30732 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30694 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq30694
    | (have j0 := eq30694 X0 X1
       grind)
    | exact resolve eq30694 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30694
  have eq30767 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30732 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30732
    | (have j0 := eq30732 X0 X1
       grind)
    | exact resolve eq30732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30732
  have eq30794 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30767 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30767
    | (have j0 := eq30767 X0 X1
       grind)
    | exact resolve eq30767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30767
  have eq30817 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30794 X0 X1
       have i₂ := eq4583 X1
       grind)
    | exact superpose eq4583 eq30794
    | (have j0 := eq30794 X0 X1
       grind)
    | exact resolve eq30794 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30794
  have eq45291 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq4153 (σ X0) X1
       grind)
    | exact superpose eq4153 eq30
    | (have j1 := eq4153 (σ X0) X1
       grind)
    | exact resolve eq30 eq4153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4153
  have eq45406 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45291 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq45291
    | (have j0 := eq45291 X0 X1
       grind)
    | exact resolve eq45291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45291
  have eq45515 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45406 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45406
    | (have j0 := eq45406 X0 X1
       grind)
    | exact resolve eq45406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45406
  have eq45614 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45515 X0 X1
       have i₂ := eq4254 X1
       grind)
    | exact superpose eq4254 eq45515
    | (have j0 := eq45515 X0 X1
       grind)
    | exact resolve eq45515 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254 eq45515
  have eq45697 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45614 X0 X1
       have i₂ := eq4583 X1
       grind)
    | exact superpose eq4583 eq45614
    | (have j0 := eq45614 X0 X1
       grind)
    | exact resolve eq45614 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4583 eq45614
  have eq45751 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45697 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45697
    | (have j0 := eq45697 X0 X1
       grind)
    | exact resolve eq45697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45697
  have eq48499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq45751 X0 X1
       grind)
    | exact superpose eq45751 eq11
    | (have j1 := eq45751 X0 X1
       grind)
    | exact resolve eq11 eq45751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45751
  have eq49102 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48499 x y
       grind)
    | exact superpose eq48499 eq16
    | (have j1 := eq48499 x y
       grind)
    | exact resolve eq16 eq48499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48499
  have eq50356 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq49102
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq49102
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq49102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq49102
       have i₂ := eq851 y x
       grind)
    | exact superpose eq851 eq49102
    | (have j1 := eq851 y x
       grind)
    | (have r₁ := eq49102
       have r₂ := eq851 y x
       grind)
    | exact resolve eq49102 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq49102
  have eq50358 : (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq50357
  have eq50359 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq50356
  have eq50360 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq50359
  have eq50362 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq50358
       have r₂ := eq13 x y
       grind)
    | exact resolve eq50358 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50358
  have eq50463 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30817 x y
       have i₂ := eq50362
       grind)
    | exact superpose eq50362 eq30817
    | (have j0 := eq30817 x y
       grind)
    | exact resolve eq30817 eq50362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30817 eq50362
  have eq50468 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq50463
  have eq50469 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq50468
  have eq50489 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50469
       grind)
    | exact superpose eq50469 eq16
    | exact resolve eq16 eq50469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50469
  have eq50638 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50489
       have i₂ := eq50360
       grind)
    | exact superpose eq50360 eq50489
    | exact resolve eq50489 eq50360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50360 eq50489
  have eq50639 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq50638
  have eq50640 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq50639
  have eq50671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5355 y
       have i₂ := eq50640
       grind)
    | exact superpose eq50640 eq5355
    | exact resolve eq5355 eq50640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50640
  have eq50705 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq50671
       have r₂ := eq16
       grind)
    | exact resolve eq50671 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50671
  have eq50837 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq50705
       grind)
    | exact superpose eq50705 eq10
    | exact resolve eq10 eq50705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50705
  have eq50998 : x = (M.op y y) := by
    first
    | (have i₁ := eq50837
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq50837
    | exact resolve eq50837 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50837
  have eq51163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5355 y
       have i₂ := eq50998
       grind)
    | exact superpose eq50998 eq5355
    | exact resolve eq5355 eq50998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5355 eq50998
  have eq51198 : False := by grind
  exact eq51198
