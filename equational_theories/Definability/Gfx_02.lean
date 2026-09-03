import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V0_Equation2536 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X1 X0) X2) X1 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq9
    | (have j1 := eq25 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq40 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34
    | (have j0 := eq34 X0
       grind)
    | exact resolve eq34 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq43 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq26
    | (have j0 := eq26 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq9
    | (have j1 := eq26 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq57 X0 x x X3 X4
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq57
    | exact resolve eq57 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq171 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  clear eq48
  have eq184 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq171 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq171
    | (have j0 := eq171 X0
       grind)
    | exact resolve eq171 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq204 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq30 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq30 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (M.op X2 (M.op (M.op X2 (σ X0)) X3)) (σ (k X0 X1))) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (σ X0) X2 X3 (σ X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq16
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq16 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq276 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 x X0
       have i₂ := eq67 X0 X0 x
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 X0 X0
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq67
    | exact resolve eq67 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq329 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       have j1 := eq40 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq361 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq67
    | exact resolve eq67 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq17 X0 X0 X1
       grind)
    | exact superpose eq17 eq361
    | exact resolve eq361 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq361
  have eq940 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq366 X0 X1
       grind)
    | exact superpose eq366 eq16
    | exact resolve eq16 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq941 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq366 X0 X1
       grind)
    | exact superpose eq366 eq8
    | exact resolve eq8 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 X1
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq941
    | exact resolve eq941 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq964 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq940 X0 X1 X2
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq940
    | exact resolve eq940 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq940
  have eq967 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq964 x X1 X2
       have i₂ := eq963 x (M.op X1 X2)
       grind)
    | exact superpose eq963 eq964
    | exact resolve eq964 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1083 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X1 X0
       have i₂ := eq963 X1 X0
       grind)
    | exact superpose eq963 eq366
    | exact resolve eq366 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq1086 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 X1 X0
       have i₂ := eq963 X1 X0
       grind)
    | exact superpose eq963 eq67
    | exact resolve eq67 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1128 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) ∨ (τ X0) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X1) X0
       have i₂ := eq963 X1 (τ X0)
       grind)
    | exact superpose eq963 eq43
    | (have j0 := eq43 (M.op X1 X1) X0
       grind)
    | exact resolve eq43 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1133 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 ∨ (τ X0) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1128 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1128
    | (have j0 := eq1128 X0 X1
       grind)
    | exact resolve eq1128 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1152 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ (M.op X1 X1)) X0) = X0 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1133 X0 X1
       have i₂ := eq1086 X1 X1
       grind)
    | exact superpose eq1086 eq1133
    | (have j0 := eq1133 X0 X1
       grind)
    | exact resolve eq1133 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq1133
  have eq1153 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq204
       have i₂ := eq19 y x
       grind)
    | exact superpose eq19 eq204
    | (have j1 := eq19 y x
       grind)
    | exact resolve eq204 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq204
  have eq1381 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq1373
  have eq1391 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1083 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq1083 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq1083
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq1083 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3522 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op X1 X1))) X0) ∨ (τ (σ (M.op X1 X1))) = X0 ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ (M.op X1 X1)) X0
       have i₂ := eq1153 (σ X0) X1
       grind)
    | exact superpose eq1153 eq39
    | (have j0 := eq39 (σ X0) (k (τ (σ (M.op X1 X1))) X0)
       have j1 := eq1153 (σ X0) X1
       grind)
    | exact resolve eq39 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq3532 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 X1) X0) ∨ (τ (σ (M.op X1 X1))) = X0 ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3522 X0 X1
       have i₂ := eq9 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq3522
    | (have j0 := eq3522 X0 X1
       grind)
    | exact resolve eq3522 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522
  have eq3543 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 ∨ (τ (σ (M.op X1 X1))) = X0 ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3532 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3532
    | (have j0 := eq3532 X0 X1
       grind)
    | exact resolve eq3532 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3544 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (M.op X1 X1) X0) = X0 ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3543 X0 X1
       have i₂ := eq9 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq3543
    | (have j0 := eq3543 X0 X1
       grind)
    | exact resolve eq3543 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543
  have eq3545 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3544 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3544
    | (have j0 := eq3544 X0 X1
       grind)
    | exact resolve eq3544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq3546 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3545 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq9570 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X1 (M.op (M.op X1 (σ X0)) X2)) (σ X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    grind
  clear eq207
  have eq9740 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9570 X0 x x
       have i₂ := eq8 (σ X0) x x
       grind)
    | exact superpose eq8 eq9570
    | (have j0 := eq9570 X0 x x
       grind)
    | exact resolve eq9570 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9570
  have eq9777 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq1381
  have eq15870 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq39 (σ x) y
       have i₂ := eq9777
       grind)
    | exact superpose eq9777 eq39
    | (have j0 := eq39 (σ x) (k (τ (σ x)) y)
       grind)
    | exact resolve eq39 eq9777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq9777
  have eq15892 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq15870
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq15870
    | exact resolve eq15870 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15870
  have eq15893 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y := by grind
  clear eq15892
  have eq15902 : x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq15893
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq15893
    | exact resolve eq15893 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15893
  have eq15903 : x = (k x y) ∨ x = y := by grind
  clear eq15902
  have eq16468 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15903
       grind)
    | exact superpose eq15903 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq15903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16479 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1391 y x X0
       have i₂ := eq15903
       grind)
    | exact superpose eq15903 eq1391
    | (have j0 := eq1391 y x X0
       grind)
    | exact resolve eq1391 eq15903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391 eq15903
  have eq17732 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq967 x y
       have i₂ := eq16468
       grind)
    | exact superpose eq16468 eq967
    | exact resolve eq967 eq16468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq16468
  have eq18410 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1083 X0 x
       have i₂ := eq17732
       grind)
    | exact superpose eq17732 eq1083
    | exact resolve eq1083 eq17732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17732
  have eq24640 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq963 x X0
       have i₂ := eq18410 X1
       grind)
    | exact superpose eq18410 eq963
    | (have j1 := eq18410 X1
       grind)
    | exact resolve eq963 eq18410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18410
  have eq25464 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3546 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) X0
       have i₂ := eq184 (M.op X0 X0)
       grind)
    | exact superpose eq184 eq3546
    | (have j0 := eq3546 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) X0
       have j1 := eq184 (M.op X0 X0)
       grind)
    | exact resolve eq3546 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25495 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq25464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25464
  have eq27652 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have j0 := eq24640 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24640
  have eq27653 : y = (M.op x y) ∨ x = y := by grind
  clear eq27652
  have eq28077 : ∀ X0 : G, x = y ∨ y = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16479 X0
       have i₂ := eq27653
       grind)
    | exact superpose eq27653 eq16479
    | (have j0 := eq16479 X0
       grind)
    | exact resolve eq16479 eq27653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16479 eq27653
  have eq28146 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq28077 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28077
  have eq28380 : ∀ X0 : G, (k y X0) = X0 ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3546 X0 y
       have i₂ := eq28146 y
       grind)
    | exact superpose eq28146 eq3546
    | exact resolve eq3546 eq28146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq30898 : y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq28380 (τ (M.op (σ y) (σ y)))
       grind)
    | exact superpose eq28380 eq184
    | (have j0 := eq184 y
       have j1 := eq28380 (τ (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq184 eq28380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq28380
  have eq30905 : y = (τ (M.op (σ y) (σ y))) ∨ x = y := by grind
  clear eq30898
  have eq33506 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op (σ y) (σ y))
       have i₂ := eq30905
       grind)
    | exact superpose eq30905 eq10
    | exact resolve eq10 eq30905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30905
  have eq33880 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1083 X0 (σ y)
       have i₂ := eq33506
       grind)
    | exact superpose eq33506 eq1083
    | exact resolve eq1083 eq33506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33506
  have eq35000 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq33880 (σ x)
       grind)
    | exact superpose eq33880 eq14
    | exact resolve eq14 eq33880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33880
  have eq35348 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35000
       have i₂ := eq28146 x
       grind)
    | exact superpose eq28146 eq35000
    | exact resolve eq35000 eq28146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28146 eq35000
  have eq35360 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq35348
  have eq35361 : x = y := by grind
  clear eq35360
  have eq35891 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35361
       grind)
    | exact superpose eq35361 eq14
    | exact resolve eq14 eq35361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35361
  have eq49335 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35891
       have i₂ := eq9740 x
       grind)
    | exact superpose eq9740 eq35891
    | (have j1 := eq9740 x
       grind)
    | (have r₁ := eq35891
       have r₂ := eq9740 x
       grind)
    | exact resolve eq35891 eq9740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9740
  have eq49513 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq49335
  have eq53694 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35891
       have i₂ := eq49513
       grind)
    | exact superpose eq49513 eq35891
    | exact resolve eq35891 eq49513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53740 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq963 (σ x) X0
       have i₂ := eq49513
       grind)
    | exact superpose eq49513 eq963
    | exact resolve eq963 eq49513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49513
  have eq63111 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       have i₂ := eq25495 X0
       grind)
    | exact superpose eq25495 eq10
    | exact resolve eq10 eq25495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25495
  have eq63970 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq963 (σ (M.op X0 X0)) X1
       have i₂ := eq63111 X0
       grind)
    | exact superpose eq63111 eq963
    | exact resolve eq963 eq63111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq63111
  have eq126564 : (σ x) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq53740 (σ (M.op (τ (σ x)) (τ (σ x))))
       have i₂ := eq329 (σ x)
       grind)
    | exact superpose eq329 eq53740
    | (have j1 := eq329 (σ x)
       grind)
    | exact resolve eq53740 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq53740
  have eq126675 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq126564
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq126564
    | exact resolve eq126564 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126564
  have eq126838 : x = (M.op x x) ∨ (M.op (σ x) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have r₁ := eq126675
       have r₂ := eq53694
       grind)
    | exact resolve eq126675 eq53694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53694 eq126675
  have eq126874 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq126838
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq126838
    | exact resolve eq126838 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126838
  have eq126882 : x = (M.op x x) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have r₁ := eq126874
       have r₂ := eq35891
       grind)
    | exact resolve eq126874 eq35891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126874
  have eq126886 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126882
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq126882
    | exact resolve eq126882 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126882
  have eq126887 : x = (M.op x x) := by grind
  clear eq126886
  have eq126922 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1083 X0 x
       have i₂ := eq126887
       grind)
    | exact superpose eq126887 eq1083
    | exact resolve eq1083 eq126887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq126934 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63970 x X0
       have i₂ := eq126887
       grind)
    | exact superpose eq126887 eq63970
    | exact resolve eq63970 eq126887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63970 eq126887
  have eq134951 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq35891
       have i₂ := eq126934 (σ x)
       grind)
    | exact superpose eq126934 eq35891
    | exact resolve eq35891 eq126934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35891 eq126934
  have eq135388 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq134951
       have i₂ := eq126922 x
       grind)
    | exact superpose eq126922 eq134951
    | exact resolve eq134951 eq126922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126922 eq134951
  have eq135389 : False := by grind
  exact eq135389

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation2536 : Law3.StructuralFromFin Law2536 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V0_Equation2536

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V0_Equation2712 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = X2 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq9
    | (have j1 := eq26 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq41 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35
    | (have j0 := eq35 X0
       grind)
    | exact resolve eq35 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq44 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq27
    | (have j0 := eq27 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq27 X1 X0
       grind)
    | exact superpose eq27 eq9
    | (have j1 := eq27 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq61 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x X0
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq16
    | exact resolve eq16 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq71 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq8
    | exact resolve eq8 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq140 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq20 X1 X0 X0
       grind)
    | exact superpose eq20 eq71
    | (have j1 := eq20 X1 X0 x
       grind)
    | exact resolve eq71 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq141 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (M.op X0 X1)
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq71
    | exact resolve eq71 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq202 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X1) X0 X2
       have i₂ := eq141 X0 X1
       grind)
    | exact superpose eq141 eq8
    | exact resolve eq8 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq31 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq31 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X0) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq8 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq367 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  clear eq49
  have eq381 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq367
    | (have j0 := eq367 X0
       grind)
    | exact resolve eq367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq537 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq4105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq289
       have i₂ := eq19 y x
       grind)
    | exact superpose eq19 eq289
    | (have j1 := eq19 y x
       grind)
    | exact resolve eq289 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq289
  have eq4113 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq4105
  have eq4501 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq4113
  have eq6969 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq40 (σ x) y
       have i₂ := eq4501
       grind)
    | exact superpose eq4501 eq40
    | (have j0 := eq40 (σ x) (k (τ (σ x)) y)
       grind)
    | exact resolve eq40 eq4501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq6979 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq6969
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6969
    | exact resolve eq6969 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6969
  have eq6980 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y := by grind
  clear eq6979
  have eq6983 : x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq6980
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6980
    | exact resolve eq6980 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980
  have eq6984 : x = (k x y) ∨ x = y := by grind
  clear eq6983
  have eq7331 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6984
       grind)
    | exact superpose eq6984 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6984
  have eq7677 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 y x X0
       have i₂ := eq7331
       grind)
    | exact superpose eq7331 eq8
    | exact resolve eq8 eq7331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7748 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq7677 X0
       have i₂ := eq141 x X0
       grind)
    | exact superpose eq141 eq7677
    | exact resolve eq7677 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7677
  have eq12361 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7748 y
       have i₂ := eq7331
       grind)
    | exact superpose eq7331 eq7748
    | exact resolve eq7748 eq7331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7748
  have eq12481 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq12361
  have eq12893 : x = y ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7331
       have i₂ := eq12481
       grind)
    | exact superpose eq12481 eq7331
    | exact resolve eq7331 eq12481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7331 eq12481
  have eq12970 : y = (M.op x x) ∨ x = y := by grind
  clear eq12893
  have eq13012 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  clear eq291
  have eq13180 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq537 x
       have i₂ := eq12970
       grind)
    | exact superpose eq12970 eq537
    | exact resolve eq537 eq12970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13237 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq141 x x
       have i₂ := eq12970
       grind)
    | exact superpose eq12970 eq141
    | exact resolve eq141 eq12970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12970
  have eq13255 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq13180
  have eq14123 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq140 (σ x) (σ y)
       have i₂ := eq13255
       grind)
    | exact superpose eq13255 eq140
    | (have j0 := eq140 (σ x) (σ y)
       grind)
    | exact resolve eq140 eq13255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq13255
  have eq161572 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq14
    | exact resolve eq14 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14123
  have eq161860 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq161572
       have i₂ := eq13237
       grind)
    | exact superpose eq13237 eq161572
    | exact resolve eq161572 eq13237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161572
  have eq161875 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq161860
  have eq161876 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq161875
  have eq162014 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq161876
       grind)
    | exact superpose eq161876 eq14
    | exact resolve eq14 eq161876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162061 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 (σ y) (σ x) X0
       have i₂ := eq161876
       grind)
    | exact superpose eq161876 eq8
    | exact resolve eq8 eq161876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162262 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq162061 X0
       have i₂ := eq141 (σ x) X0
       grind)
    | exact superpose eq141 eq162061
    | exact resolve eq162061 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162061
  have eq162395 : (σ x) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq162014
       have i₂ := eq13237
       grind)
    | exact superpose eq13237 eq162014
    | exact resolve eq162014 eq13237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13237 eq162014
  have eq162411 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq162395
  have eq163731 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq162262 (σ y)
       have i₂ := eq161876
       grind)
    | exact superpose eq161876 eq162262
    | exact resolve eq162262 eq161876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162262
  have eq164035 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq163731
  have eq164202 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq161876
       have i₂ := eq164035
       grind)
    | exact superpose eq164035 eq161876
    | exact resolve eq161876 eq164035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161876 eq164035
  have eq164392 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq164202
  have eq164411 : x = y := by
    first
    | (have r₁ := eq164392
       have r₂ := eq162411
       grind)
    | exact resolve eq164392 eq162411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162411 eq164392
  have eq164548 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq164411
       grind)
    | exact superpose eq164411 eq14
    | exact resolve eq14 eq164411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164411
  have eq164709 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq164548
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq164548
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq164548
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq164548
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq164548 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166848 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq164709 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164709
  have eq166984 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq537 x
       have i₂ := eq166848
       grind)
    | exact superpose eq166848 eq537
    | (have j0 := eq537 x
       grind)
    | exact resolve eq537 eq166848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq166848
  have eq167183 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq141 (σ x) (σ (M.op x x))
       have i₂ := eq166984
       grind)
    | exact superpose eq166984 eq141
    | exact resolve eq141 eq166984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167185 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq202 (σ x) (σ (M.op x x)) x
       have i₂ := eq166984
       grind)
    | exact superpose eq166984 eq202
    | exact resolve eq202 eq166984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167244 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq167185 X0
       have i₂ := eq141 (σ x) X0
       grind)
    | exact superpose eq141 eq167185
    | exact resolve eq167185 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167185
  have eq167389 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq164548
       have i₂ := eq167183
       grind)
    | exact superpose eq167183 eq164548
    | exact resolve eq164548 eq167183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167183
  have eq167957 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13012 x X0
       have i₂ := eq167244 X0
       grind)
    | exact superpose eq167244 eq13012
    | (have j0 := eq13012 x x
       grind)
    | exact resolve eq13012 eq167244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13012 eq167244
  have eq168200 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq167957 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167957
  have eq168203 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq168200 X0
       grind)
    | (have r₁ := eq168200 X0
       have r₂ := eq164548
       grind)
    | exact resolve eq168200 eq164548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168200
  have eq168282 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq166984
       have i₂ := eq168203 (σ (M.op x x))
       grind)
    | exact superpose eq168203 eq166984
    | exact resolve eq166984 eq168203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166984 eq168203
  have eq168610 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq168282
  have eq168633 : x = (M.op x x) := by
    first
    | (have r₁ := eq168610
       have r₂ := eq167389
       grind)
    | exact resolve eq168610 eq167389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167389 eq168610
  have eq168821 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq168633
       grind)
    | exact superpose eq168633 eq8
    | exact resolve eq8 eq168633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168906 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq202 x x x
       have i₂ := eq168633
       grind)
    | exact superpose eq168633 eq202
    | exact resolve eq202 eq168633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq168633
  have eq169244 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq168906 X0
       have i₂ := eq141 x X0
       grind)
    | exact superpose eq141 eq168906
    | exact resolve eq168906 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq168906
  have eq170073 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq168821 X0
       have i₂ := eq169244 X0
       grind)
    | exact superpose eq169244 eq168821
    | exact resolve eq168821 eq169244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168821
  have eq170517 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq169244 X0
       have i₂ := eq170073 X0
       grind)
    | exact superpose eq170073 eq169244
    | exact resolve eq169244 eq170073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169244
  have eq171256 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq44 x X0
       have i₂ := eq170073 (τ X0)
       grind)
    | exact superpose eq170073 eq44
    | (have j0 := eq44 x X0
       grind)
    | exact resolve eq44 eq170073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq170073
  have eq171306 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq171256 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq171256
    | (have j0 := eq171256 X0
       grind)
    | exact resolve eq171256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171256
  have eq171438 : ∀ X0 : G, (τ X0) = x ∨ (k (σ x) X0) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq171306 X0
       have i₂ := eq170517 x
       grind)
    | exact superpose eq170517 eq171306
    | (have j0 := eq171306 X0
       grind)
    | exact resolve eq171306 eq170517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171306
  have eq171439 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq171438 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171438
  have eq177055 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ x)) X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq40 (σ x) X0
       have i₂ := eq171439 (σ X0)
       grind)
    | exact superpose eq171439 eq40
    | (have j0 := eq40 (σ X0) (k (τ (σ x)) X0)
       have j1 := eq171439 (σ X0)
       grind)
    | exact resolve eq40 eq171439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq171439
  have eq177081 : ∀ X0 : G, (τ (σ X0)) = (k x X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq177055 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq177055
    | (have j0 := eq177055 X0
       grind)
    | exact resolve eq177055 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177055
  have eq177104 : ∀ X0 : G, (k x X0) = X0 ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq177081 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq177081
    | (have j0 := eq177081 X0
       grind)
    | exact resolve eq177081 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177081
  have eq177109 : ∀ X0 : G, x = X0 ∨ (k x X0) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq177104 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq177104
    | (have j0 := eq177104 X0
       grind)
    | exact resolve eq177104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177104
  have eq177110 : ∀ X0 : G, x = X0 ∨ x = X0 ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177109 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq177109
    | (have j0 := eq177109 X0
       grind)
    | exact resolve eq177109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177109
  have eq177111 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq177110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177110
  have eq177246 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq381 x
       have i₂ := eq177111 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq177111 eq381
    | (have j0 := eq381 x
       have j1 := eq177111 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq381 eq177111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq177111
  have eq177247 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq177246
  have eq177354 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq177247
       grind)
    | exact superpose eq177247 eq10
    | exact resolve eq10 eq177247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177247
  have eq177491 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq164548
       have i₂ := eq177354
       grind)
    | exact superpose eq177354 eq164548
    | exact resolve eq164548 eq177354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164548 eq177354
  have eq177815 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq177491
       have i₂ := eq170517 x
       grind)
    | exact superpose eq170517 eq177491
    | exact resolve eq177491 eq170517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170517 eq177491
  have eq177816 : False := by grind
  exact eq177816

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation2712 : Law3.StructuralFromFin Law2712 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V0_Equation2712

/-- `Equation2782`: `x = ((y ◇ z) ◇ (x ◇ w)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V0_Equation2782 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2782 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law2782.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X4 X5 : G, (M.op (M.op X0 (M.op X4 X5)) X4) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq8 X4 (M.op (M.op x x) (M.op X0 x)) X0 X5
       have i₂ := eq8 X0 x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op x x) (M.op (M.op X0 X1) x) X1
       have i₂ := eq8 (M.op X0 X1) x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X0 X1) X0
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) X0
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq16
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq20
    | (have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq20 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq20 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq25 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq68 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq69 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | (have j0 := eq63 X0
       grind)
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq71 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op X0 X1) X0
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq76 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq20 (τ X1) X0
       grind)
    | exact superpose eq20 eq31
    | (have j0 := eq31 X1 X0
       have j1 := eq20 (τ X1) X0
       grind)
    | exact resolve eq31 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq77 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq31
    | (have j0 := eq31 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq35 X0 X0 X0
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X2 (M.op X0 X1)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X3 X0) (M.op X0 X1)
       have i₂ := eq35 X0 X3 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq186 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq103 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq103
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq103 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq346 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq33 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq33 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq18
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq545 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X0
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq54
    | (have j0 := eq54 X0 X1
       have j1 := eq186 X0 X1
       grind)
    | exact resolve eq54 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq552 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq545 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq1467 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1779 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq18
    | (have j1 := eq46 X0 X1
       grind)
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1905 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (M.op (τ X0) X1) X0
       have i₂ := eq18 (τ X0) X1
       grind)
    | exact superpose eq18 eq76
    | (have j0 := eq76 (M.op (τ X0) X1) X0
       grind)
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1940 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1905 X0 X1
       have j1 := eq71 (τ X0) X1
       grind)
    | (have r₁ := eq1905 X0 X1
       have r₂ := eq71 (τ X0) X1
       grind)
    | exact resolve eq1905 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1952 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 ∨ (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1940 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1940
    | (have j0 := eq1940 X0 X1
       grind)
    | exact resolve eq1940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2052 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ (M.op X1 X1)) X0) = (σ (M.op (M.op X1 X1) (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X1 X1
       have i₂ := eq77 (M.op X1 X1) X0
       grind)
    | exact superpose eq77 eq35
    | (have j1 := eq77 (M.op X1 X1) X0
       grind)
    | exact resolve eq35 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq77
  have eq2081 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = (σ (M.op (M.op X1 X1) (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2052 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq3392 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq346
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq346
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq346 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq346
       have i₂ := eq26 y x
       grind)
    | exact superpose eq26 eq346
    | (have j1 := eq26 y x
       grind)
    | exact resolve eq346 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq3404 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq3396
  have eq3408 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq3392
  have eq4330 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq353
  have eq4610 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by grind
  have eq4626 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq25 (σ x) (σ x)
       have i₂ := eq3404
       grind)
    | exact superpose eq3404 eq25
    | exact resolve eq25 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5122 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25 (σ x) (σ x)
       have i₂ := eq3408
       grind)
    | exact superpose eq3408 eq25
    | exact resolve eq25 eq3408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3408
  have eq6966 : (σ x) = (σ (k x y)) ∨ x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq4610
       grind)
    | exact superpose eq4610 eq13
    | (have j0 := eq13 (σ x) (σ (k x y))
       grind)
    | exact resolve eq13 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610
  have eq6983 : (σ x) = (σ (k x y)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq6966
  have eq7896 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6983
       have i₂ := eq26 y x
       grind)
    | exact superpose eq26 eq6983
    | (have j1 := eq26 y x
       grind)
    | exact resolve eq6983 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6983
  have eq7940 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq7896
  have eq10414 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4626
       grind)
    | exact superpose eq4626 eq14
    | exact resolve eq14 eq4626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4626
  have eq10847 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10414
       have i₂ := eq7940
       grind)
    | exact superpose eq7940 eq10414
    | exact resolve eq10414 eq7940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7940 eq10414
  have eq10849 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq10847
  have eq24294 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5122
       grind)
    | exact superpose eq5122 eq14
    | exact resolve eq14 eq5122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5122
  have eq28337 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2081 X0 (τ X0)
       have i₂ := eq18 (τ X0) (τ X0)
       grind)
    | exact superpose eq18 eq2081
    | (have j0 := eq2081 X0 (τ X0)
       grind)
    | exact resolve eq2081 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq28481 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq28337 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28337
    | (have j0 := eq28337 X0
       grind)
    | exact resolve eq28337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28337
  have eq37441 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) X1))) X0) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = X0 ∨ (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ (M.op (τ (σ X0)) X1)) X0
       have i₂ := eq1952 (σ X0) X1
       grind)
    | exact superpose eq1952 eq68
    | (have j0 := eq68 (σ X0) (k (τ (σ (M.op (τ (σ X0)) X1))) X0)
       have j1 := eq1952 (σ X0) X1
       grind)
    | exact resolve eq68 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq37464 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) X0) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = X0 ∨ (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37441 X0 X1
       have i₂ := eq9 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq9 eq37441
    | (have j0 := eq37441 X0 X1
       grind)
    | exact resolve eq37441 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37441
  have eq37497 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (τ (σ (M.op (τ (σ X0)) X1))) = X0 ∨ (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37464 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37464
    | (have j0 := eq37464 X0 X1
       grind)
    | exact resolve eq37464 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37464
  have eq37513 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37497 X0 X1
       have i₂ := eq9 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq9 eq37497
    | (have j0 := eq37497 X0 X1
       grind)
    | exact resolve eq37497 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37497
  have eq37527 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37513 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37513
    | (have j0 := eq37513 X0 X1
       grind)
    | exact resolve eq37513 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37513
  have eq37541 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37527 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37527
    | (have j0 := eq37527 X0 X1
       grind)
    | exact resolve eq37527 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37527
  have eq37553 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37541 X0 X1
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq37541 X0 X1
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq37541 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq37541
  have eq37778 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 (M.op X0 X1)
       have i₂ := eq37553 X0 X1
       grind)
    | exact superpose eq37553 eq552
    | (have j0 := eq552 X0 X1
       have j1 := eq37553 X0 X1
       grind)
    | exact resolve eq552 eq37553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37802 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37825 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37778 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq37778
    | (have j0 := eq37778 X0 X1
       grind)
    | exact resolve eq37778 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37778
  have eq37853 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37825 X0 X0
       have j1 := eq37802 X0 X1
       grind)
    | (have r₁ := eq37825 X0 X1
       have r₂ := eq37802 X0 X1
       grind)
    | (have r₁ := eq37825 X1 X1
       have r₂ := eq37802 X1 X1
       grind)
    | exact resolve eq37825 eq37802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37825
  have eq39143 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq37853 (σ x) (σ x)
       have i₂ := eq3404
       grind)
    | exact superpose eq3404 eq37853
    | exact resolve eq37853 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq39284 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq39143
       have r₂ := eq10849
       grind)
    | exact resolve eq39143 eq10849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10849 eq39143
  have eq53937 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq82 y (σ x)
       have i₂ := eq39284
       grind)
    | exact superpose eq39284 eq82
    | (have j0 := eq82 (k y (τ (σ x))) (σ x)
       grind)
    | exact resolve eq82 eq39284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq39284
  have eq54010 : x = (k y x) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53937
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq53937
    | exact resolve eq53937 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53937
  have eq54035 : x = y ∨ x = (k y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq54010
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq54010
    | exact resolve eq54010 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54010
  have eq54036 : x = (k y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq54035
  have eq54445 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq54036
       grind)
    | exact superpose eq54036 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq54036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54036
  have eq54478 : x = (M.op y x) ∨ x = y := by grind
  clear eq54445
  have eq54959 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18 y x
       have i₂ := eq54478
       grind)
    | exact superpose eq54478 eq18
    | exact resolve eq18 eq54478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54478
  have eq55144 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq24294
       have i₂ := eq54959
       grind)
    | exact superpose eq54959 eq24294
    | exact resolve eq24294 eq54959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24294
  have eq55287 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq55144
  have eq55288 : y = (M.op x x) ∨ x = y := by grind
  clear eq55287
  have eq55971 : x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq37853 x x
       have i₂ := eq55288
       grind)
    | exact superpose eq55288 eq37853
    | exact resolve eq37853 eq55288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37853 eq55288
  have eq55986 : x = (k y x) ∨ x = y := by grind
  clear eq55971
  have eq56871 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1779 y x
       have i₂ := eq55986
       grind)
    | exact superpose eq55986 eq1779
    | (have j0 := eq1779 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1779 eq55986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq55986
  have eq56877 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq56871
  have eq117823 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq56877
       grind)
    | exact superpose eq56877 eq14
    | exact resolve eq14 eq56877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56877
  have eq118439 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq117823
       have i₂ := eq54959
       grind)
    | exact superpose eq54959 eq117823
    | exact resolve eq117823 eq54959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54959 eq117823
  have eq118456 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq118439
  have eq118457 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq118456
  have eq118897 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq118457
       grind)
    | exact superpose eq118457 eq9
    | exact resolve eq9 eq118457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118457
  have eq119051 : x = y ∨ x = y := by
    first
    | (have i₁ := eq118897
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq118897
    | exact resolve eq118897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118897
  have eq119052 : x = y := by grind
  clear eq119051
  have eq119405 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq119052
       grind)
    | exact superpose eq119052 eq14
    | exact resolve eq14 eq119052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119052
  have eq119886 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq119405
       have i₂ := eq4330 x
       grind)
    | exact superpose eq4330 eq119405
    | (have j1 := eq4330 x
       grind)
    | (have r₁ := eq119405
       have r₂ := eq4330 x
       grind)
    | exact resolve eq119405 eq4330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330
  have eq119887 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq119405
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq119405
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq119405
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq119405
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq119405 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119888 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq119405
       have i₂ := eq552 (σ x) X0
       grind)
    | exact superpose eq552 eq119405
    | (have j1 := eq552 (σ x) X0
       grind)
    | exact resolve eq119405 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq119891 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq119886
  have eq124843 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq119405
       have i₂ := eq119891
       grind)
    | exact superpose eq119891 eq119405
    | exact resolve eq119405 eq119891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119891
  have eq128646 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq119887 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119887
  have eq130467 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1467 x
       have i₂ := eq128646
       grind)
    | exact superpose eq128646 eq1467
    | (have j0 := eq1467 x
       grind)
    | exact resolve eq1467 eq128646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq128646
  have eq279291 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28481 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq28481
    | exact resolve eq28481 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28481
  have eq281327 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq279291 X0
       grind)
    | exact superpose eq279291 eq54
    | (have j0 := eq54 (σ X0) (σ (M.op X0 X0))
       have j1 := eq279291 X0
       grind)
    | exact resolve eq54 eq279291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279291
  have eq281334 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq281327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281327
  have eq284108 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq281334 X0
       grind)
    | exact superpose eq281334 eq18
    | (have j1 := eq281334 X0
       grind)
    | exact resolve eq18 eq281334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281334
  have eq286572 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq130467
       have i₂ := eq284108 x
       grind)
    | exact superpose eq284108 eq130467
    | (have j1 := eq284108 x
       grind)
    | exact resolve eq130467 eq284108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130467 eq284108
  have eq286666 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq286572
  have eq286675 : x = (M.op x x) := by
    first
    | (have r₁ := eq286666
       have r₂ := eq124843
       grind)
    | exact resolve eq286666 eq124843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124843 eq286666
  have eq287916 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq119888 X0
       have i₂ := eq286675
       grind)
    | exact superpose eq286675 eq119888
    | (have j0 := eq119888 X0
       grind)
    | exact resolve eq119888 eq286675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119888
  have eq288007 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X1 x) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 x x X1 X0
       have i₂ := eq286675
       grind)
    | exact superpose eq286675 eq106
    | exact resolve eq106 eq286675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq288211 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq287916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287916
  have eq293278 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ X0) x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq68 X0 x
       have i₂ := eq288211 X0
       grind)
    | exact superpose eq288211 eq68
    | (have j0 := eq68 (M.op X0 (σ x)) (k (τ X0) x)
       grind)
    | exact resolve eq68 eq288211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq288211
  have eq297758 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (k (M.op X0 x) X1) ∨ (M.op X0 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 (M.op X0 x) X1
       have i₂ := eq288007 X0 X0
       grind)
    | exact superpose eq288007 eq102
    | exact resolve eq102 eq288007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq288007
  have eq333973 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq293278 (M.op (σ x) X0)
       have i₂ := eq18 (σ x) X0
       grind)
    | exact superpose eq18 eq293278
    | (have j0 := eq293278 (M.op (σ x) X0)
       grind)
    | exact resolve eq293278 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293278
  have eq334038 : ∀ X0 : G, x = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq333973 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq333973
    | (have j0 := eq333973 X0
       grind)
    | exact resolve eq333973 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333973
  have eq422469 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) X0) ∨ (M.op X0 x) = X0 ∨ (k (M.op X0 x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq297758 X0 X0
       have i₂ := eq37553 X0 x
       grind)
    | exact superpose eq37553 eq297758
    | (have j0 := eq297758 X0 (M.op (M.op X0 x) X0)
       have j1 := eq37553 X0 x
       grind)
    | exact resolve eq297758 eq37553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37553 eq297758
  have eq422533 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) X0) ∨ (k (M.op X0 x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq422469 X0
       have j1 := eq37802 X0 x
       grind)
    | (have r₁ := eq422469 x
       have r₂ := eq37802 (M.op x x) x
       grind)
    | (have r₁ := eq422469 X0
       have r₂ := eq37802 X0 x
       grind)
    | exact resolve eq422469 eq37802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422469
  have eq422534 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (k (M.op X0 x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq422533 X0
       have i₂ := eq18 X0 x
       grind)
    | exact superpose eq18 eq422533
    | (have j0 := eq422533 X0
       grind)
    | exact resolve eq422533 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq422533
  have eq422535 : ∀ X0 : G, (k (M.op X0 x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq422534 X0
       have j1 := eq37802 X0 x
       grind)
    | (have r₁ := eq422534 X0
       have r₂ := eq37802 X0 x
       grind)
    | exact resolve eq422534 eq37802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37802 eq422534
  have eq424152 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) x)) X0) ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op (τ X0) x)
       have i₂ := eq422535 (τ X0)
       grind)
    | exact superpose eq422535 eq31
    | (have j0 := eq31 X0 (M.op (τ X0) x)
       grind)
    | exact resolve eq31 eq422535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq422535
  have eq424164 : ∀ X0 : G, (k (σ (M.op (τ X0) x)) X0) = X0 ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq424152 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq424152
    | (have j0 := eq424152 X0
       grind)
    | exact resolve eq424152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424152
  have eq430484 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x (τ (M.op (σ x) X0))
       have i₂ := eq334038 X0
       grind)
    | exact superpose eq334038 eq54
    | (have j0 := eq54 x (τ (M.op (σ x) X0))
       have j1 := eq334038 X0
       grind)
    | exact resolve eq54 eq334038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq334038
  have eq430491 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq430484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430484
  have eq445924 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq424164 (M.op (σ x) X0)
       have i₂ := eq430491 X0
       grind)
    | exact superpose eq430491 eq424164
    | (have j1 := eq430491 X0
       grind)
    | exact resolve eq424164 eq430491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424164 eq430491
  have eq446112 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq445924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445924
  have eq937577 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq446112
  have eq937588 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq937577
       grind)
    | exact superpose eq937577 eq10
    | exact resolve eq10 eq937577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937577
  have eq937589 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq937588
  have eq937626 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq119405
       have i₂ := eq937589
       grind)
    | exact superpose eq937589 eq119405
    | exact resolve eq119405 eq937589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119405 eq937589
  have eq938218 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq937626
       have i₂ := eq286675
       grind)
    | exact superpose eq286675 eq937626
    | exact resolve eq937626 eq286675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286675 eq937626
  have eq938219 : False := by grind
  exact eq938219

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation2782 : Law3.StructuralFromFin Law2782 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V0_Equation2782

/-- `Equation3145`: `x = (((y ◇ y) ◇ x) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V0_Equation3145 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3145 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law3145.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X2 : G, (M.op (M.op X0 X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq8 X0 (M.op (M.op x x) X0) X2
       have i₂ := eq8 X0 x (M.op (M.op x x) X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) X0
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq17 X0 (M.op X0 X0)
       grind)
    | exact superpose eq17 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1) X0
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq16
    | exact resolve eq16 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq64 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq43 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq31
  have eq85 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78
    | (have j0 := eq78 X0
       grind)
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq102 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq9
    | (have j1 := eq32 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq280 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq34 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq34 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X0) (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq34
  have eq386 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  clear eq102
  have eq403 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq386 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq386
    | (have j0 := eq386 X0
       grind)
    | exact resolve eq386 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq413 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq85
    | exact resolve eq85 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1045 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq280
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq280
    | (have j1 := eq20 y x
       grind)
    | exact resolve eq280 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq280
  have eq1055 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq1045
  have eq1770 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq286
  have eq10402 : x = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq403 x
       have i₂ := eq1055
       grind)
    | exact superpose eq1055 eq403
    | exact resolve eq403 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq10471 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq44 X0 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))
       have i₂ := eq403 (M.op X0 X0)
       grind)
    | exact superpose eq403 eq44
    | (have j0 := eq44 X0 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))
       have j1 := eq403 (M.op X0 X0)
       grind)
    | exact resolve eq44 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10498 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq10471 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10471
  have eq10545 : x = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq10402
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10402
    | exact resolve eq10402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10402
  have eq10546 : x = (k x y) ∨ x = (τ (σ y)) ∨ x = y := by grind
  clear eq10545
  have eq10574 : x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq10546
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10546
    | exact resolve eq10546 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10546
  have eq10575 : x = (k x y) ∨ x = y := by grind
  clear eq10574
  have eq10624 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq64 y x X0
       have i₂ := eq10575
       grind)
    | exact superpose eq10575 eq64
    | (have j0 := eq64 y x X0
       grind)
    | exact resolve eq64 eq10575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq10575
  have eq11709 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26 x y
       have i₂ := eq10624 X0
       grind)
    | exact superpose eq10624 eq26
    | (have j1 := eq10624 X0
       grind)
    | exact resolve eq26 eq10624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq13083 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq17 x X0
       have i₂ := eq11709 X1
       grind)
    | exact superpose eq11709 eq17
    | (have j1 := eq11709 X1
       grind)
    | exact resolve eq17 eq11709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11709
  have eq14327 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have j0 := eq13083 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13083
  have eq14328 : y = (M.op x y) ∨ x = y := by grind
  clear eq14327
  have eq14671 : ∀ X0 : G, x = y ∨ y = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10624 X0
       have i₂ := eq14328
       grind)
    | exact superpose eq14328 eq10624
    | (have j0 := eq10624 X0
       grind)
    | exact resolve eq10624 eq14328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10624 eq14328
  have eq14682 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq14671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14671
  have eq15371 : ∀ X0 : G, (k y X0) = X0 ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44 y x
       have i₂ := eq14682 y
       grind)
    | exact superpose eq14682 eq44
    | exact resolve eq44 eq14682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq17117 : y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq403 y
       have i₂ := eq15371 (τ (M.op (σ y) (σ y)))
       grind)
    | exact superpose eq15371 eq403
    | (have j0 := eq403 y
       have j1 := eq15371 (τ (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq403 eq15371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq15371
  have eq17126 : y = (τ (M.op (σ y) (σ y))) ∨ x = y := by grind
  clear eq17117
  have eq18664 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op (σ y) (σ y))
       have i₂ := eq17126
       grind)
    | exact superpose eq17126 eq10
    | exact resolve eq10 eq17126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17126
  have eq19185 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq43 X0 (σ y)
       have i₂ := eq18664
       grind)
    | exact superpose eq18664 eq43
    | exact resolve eq43 eq18664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18664
  have eq20020 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq19185 (σ x)
       grind)
    | exact superpose eq19185 eq14
    | exact resolve eq14 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19185
  have eq20512 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq20020
       have i₂ := eq14682 x
       grind)
    | exact superpose eq14682 eq20020
    | exact resolve eq20020 eq14682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14682 eq20020
  have eq20515 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq20512
  have eq20516 : x = y := by grind
  clear eq20515
  have eq20808 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20516
       grind)
    | exact superpose eq20516 eq14
    | exact resolve eq14 eq20516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20516
  have eq21298 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq20808
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq20808
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq20808
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq20808
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq20808 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28984 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       have i₂ := eq10498 X0
       grind)
    | exact superpose eq10498 eq10
    | exact resolve eq10 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq29424 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ (M.op X0 X0)) X1
       have i₂ := eq28984 X0
       grind)
    | exact superpose eq28984 eq17
    | exact resolve eq17 eq28984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq29427 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (σ (M.op X0 X0))
       have i₂ := eq28984 X0
       grind)
    | exact superpose eq28984 eq43
    | exact resolve eq43 eq28984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28984
  have eq42749 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20808
       have i₂ := eq1770 x
       grind)
    | exact superpose eq1770 eq20808
    | (have j1 := eq1770 x
       grind)
    | (have r₁ := eq20808
       have r₂ := eq1770 x
       grind)
    | exact resolve eq20808 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq42861 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq42749
  have eq42912 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20808
       have i₂ := eq42861
       grind)
    | exact superpose eq42861 eq20808
    | exact resolve eq20808 eq42861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42861
  have eq68040 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq21298 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21298
  have eq68041 : (σ (M.op x x)) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq68040
       have i₂ := eq29427 x (σ x)
       grind)
    | exact superpose eq29427 eq68040
    | exact resolve eq68040 eq29427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29427 eq68040
  have eq68997 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq413 x
       have i₂ := eq68041
       grind)
    | exact superpose eq68041 eq413
    | (have j0 := eq413 x
       grind)
    | exact resolve eq413 eq68041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq68041
  have eq69091 : x = (M.op x x) := by
    first
    | (have r₁ := eq68997
       have r₂ := eq42912
       grind)
    | exact resolve eq68997 eq42912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42912 eq68997
  have eq70342 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq43 X0 x
       have i₂ := eq69091
       grind)
    | exact superpose eq69091 eq43
    | exact resolve eq43 eq69091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70359 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29424 x X0
       have i₂ := eq69091
       grind)
    | exact superpose eq69091 eq29424
    | exact resolve eq29424 eq69091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29424 eq69091
  have eq73383 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20808
       have i₂ := eq70359 (σ x)
       grind)
    | exact superpose eq70359 eq20808
    | exact resolve eq20808 eq70359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20808 eq70359
  have eq73525 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq73383
       have i₂ := eq70342 x
       grind)
    | exact superpose eq70342 eq73383
    | exact resolve eq73383 eq70342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70342 eq73383
  have eq73526 : False := by grind
  exact eq73526

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation3145 : Law3.StructuralFromFin Law3145 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V0_Equation3145

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V0_Equation3180 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X1 X2
       have i₂ := eq12 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op (M.op X1 X2) X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X2) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X0 X1) X0
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) X0
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq20
    | (have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq20 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq49 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq54 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9
    | (have j1 := eq28 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq55 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X0
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq27 X1 X2 X0
       grind)
    | exact superpose eq27 eq18
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq29
    | (have j0 := eq29 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq9
    | (have j1 := eq29 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq208 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq31 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq31 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq291 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq22 X0 X0 X0
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq22 X1 X0 X0
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq305 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq291
    | (have j0 := eq291 X0 X1
       grind)
    | exact resolve eq291 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq331 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  clear eq80
  have eq347 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq331 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq331
    | (have j0 := eq331 X0
       grind)
    | exact resolve eq331 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq408 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq827 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq18
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq18 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1800 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq208
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq208
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq208 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq1802 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq1800
  have eq2123 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq1802
  have eq2704 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (τ (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54 (σ x) y
       have i₂ := eq2123
       grind)
    | exact superpose eq2123 eq54
    | (have j0 := eq54 (σ x) (k (τ (σ x)) y)
       grind)
    | exact resolve eq54 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq2713 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2704
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2704
    | exact resolve eq2704 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq2715 : x = y ∨ x = (k x y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2713
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2713
    | exact resolve eq2713 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2713
  have eq2716 : x = (k x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq2715
  have eq2830 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2716
       grind)
    | exact superpose eq2716 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2837 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq2830
  have eq3026 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27 x y X0
       have i₂ := eq2837
       grind)
    | exact superpose eq2837 eq27
    | exact resolve eq27 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3067 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3026 X0
       have i₂ := eq18 x X0
       grind)
    | exact superpose eq18 eq3026
    | exact resolve eq3026 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3646 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq305 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq3652 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3646 X0
       grind)
    | (have r₁ := eq3646 x
       have r₂ := eq18 x x
       grind)
    | exact resolve eq3646 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq3968 : x = y ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2837
       have i₂ := eq3067 y
       grind)
    | exact superpose eq3067 eq2837
    | exact resolve eq2837 eq3067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837 eq3067
  have eq4017 : y = (M.op x x) ∨ x = y := by grind
  clear eq3968
  have eq4265 : x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq3652 x
       have i₂ := eq4017
       grind)
    | exact superpose eq4017 eq3652
    | exact resolve eq3652 eq4017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq4274 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq4017
       grind)
    | exact superpose eq4017 eq24
    | exact resolve eq24 eq4017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4017
  have eq4311 : x = (k y x) ∨ x = y := by grind
  clear eq4265
  have eq34501 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq827 y x
       have i₂ := eq4311
       grind)
    | exact superpose eq4311 eq827
    | (have j0 := eq827 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq827 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq4311
  have eq34692 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34501
  have eq38739 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq34692
       grind)
    | exact superpose eq34692 eq14
    | exact resolve eq14 eq34692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34692
  have eq39274 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq38739
       have i₂ := eq4274
       grind)
    | exact superpose eq4274 eq38739
    | exact resolve eq38739 eq4274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274 eq38739
  have eq39282 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq39274
  have eq39283 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq39282
  have eq39491 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq39283
       grind)
    | exact superpose eq39283 eq9
    | exact resolve eq9 eq39283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39283
  have eq39593 : x = y ∨ x = y := by
    first
    | (have i₁ := eq39491
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq39491
    | exact resolve eq39491 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39491
  have eq39594 : x = y := by grind
  clear eq39593
  have eq39916 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq39594
       grind)
    | exact superpose eq39594 eq14
    | exact resolve eq14 eq39594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39594
  have eq40410 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq39916
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq39916
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq39916
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq39916
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq39916 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41366 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq40410 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40410
  have eq41575 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq408 x
       have i₂ := eq41366
       grind)
    | exact superpose eq41366 eq408
    | (have j0 := eq408 x
       grind)
    | exact resolve eq408 eq41366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq41366
  have eq42158 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq27 (σ x) (σ (M.op x x)) X0
       have i₂ := eq41575
       grind)
    | exact superpose eq41575 eq27
    | exact resolve eq27 eq41575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42301 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq42158 X0
       have i₂ := eq18 (σ x) X0
       grind)
    | exact superpose eq18 eq42158
    | exact resolve eq42158 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42158
  have eq42650 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39916
       have i₂ := eq42301 (σ x)
       grind)
    | exact superpose eq42301 eq39916
    | exact resolve eq39916 eq42301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42655 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41575
       have i₂ := eq42301 (σ (M.op x x))
       grind)
    | exact superpose eq42301 eq41575
    | exact resolve eq41575 eq42301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41575 eq42301
  have eq42809 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq42655
  have eq42820 : x = (M.op x x) := by
    first
    | (have r₁ := eq42650
       have r₂ := eq42809
       grind)
    | exact resolve eq42650 eq42809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42650 eq42809
  have eq43113 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27 x x X0
       have i₂ := eq42820
       grind)
    | exact superpose eq42820 eq27
    | exact resolve eq27 eq42820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq43124 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 x x
       have i₂ := eq42820
       grind)
    | exact superpose eq42820 eq71
    | exact resolve eq71 eq42820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq42820
  have eq43225 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq43124 x
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq43124
    | exact resolve eq43124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43124
  have eq43228 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43113 X0
       have i₂ := eq18 x X0
       grind)
    | exact superpose eq18 eq43113
    | exact resolve eq43113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq43113
  have eq44680 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq75 x X0
       have i₂ := eq43228 (τ X0)
       grind)
    | exact superpose eq43228 eq75
    | (have j0 := eq75 x X0
       grind)
    | exact resolve eq75 eq43228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq43228
  have eq44696 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq44680 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44680
    | (have j0 := eq44680 X0
       grind)
    | exact resolve eq44680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44680
  have eq44724 : ∀ X0 : G, (τ X0) = x ∨ (k (σ x) X0) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq44696 X0
       have i₂ := eq43225 x
       grind)
    | exact superpose eq43225 eq44696
    | (have j0 := eq44696 X0
       grind)
    | exact resolve eq44696 eq43225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44696
  have eq44725 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq44724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44724
  have eq47167 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ x)) X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq54 (σ x) X0
       have i₂ := eq44725 (σ X0)
       grind)
    | exact superpose eq44725 eq54
    | (have j0 := eq54 (σ X0) (k (τ (σ x)) X0)
       have j1 := eq44725 (σ X0)
       grind)
    | exact resolve eq54 eq44725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq44725
  have eq47215 : ∀ X0 : G, (τ (σ X0)) = (k x X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq47167 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq47167
    | (have j0 := eq47167 X0
       grind)
    | exact resolve eq47167 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47167
  have eq47236 : ∀ X0 : G, (k x X0) = X0 ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq47215 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47215
    | (have j0 := eq47215 X0
       grind)
    | exact resolve eq47215 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47215
  have eq47244 : ∀ X0 : G, x = X0 ∨ (k x X0) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq47236 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq47236
    | (have j0 := eq47236 X0
       grind)
    | exact resolve eq47236 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47236
  have eq47256 : ∀ X0 : G, x = X0 ∨ x = X0 ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47244 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47244
    | (have j0 := eq47244 X0
       grind)
    | exact resolve eq47244 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47244
  have eq47257 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq47256 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47256
  have eq47683 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq347 x
       have i₂ := eq47257 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq47257 eq347
    | (have j0 := eq347 x
       have j1 := eq47257 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq347 eq47257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq47257
  have eq47688 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq47683
  have eq47865 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq47688
       grind)
    | exact superpose eq47688 eq10
    | exact resolve eq10 eq47688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47688
  have eq48719 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq39916
       have i₂ := eq47865
       grind)
    | exact superpose eq47865 eq39916
    | exact resolve eq39916 eq47865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39916 eq47865
  have eq48886 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq48719
       have i₂ := eq43225 x
       grind)
    | exact superpose eq43225 eq48719
    | exact resolve eq48719 eq43225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43225 eq48719
  have eq48887 : False := by grind
  exact eq48887

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation3180 : Law3.StructuralFromFin Law3180 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V0_Equation3180
