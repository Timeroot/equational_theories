import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1246`: `x = x ◇ (((y ◇ x) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V1_Equation1246 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1246 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law1246.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X0) X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 (M.op X0 X1)) X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op (M.op X2 (M.op X0 X1)) X3) X3)
       have i₂ := eq8 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1 x x
       have i₂ := eq8 (M.op X0 X1) x x
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 X1))) = X1 ∨ (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X2 X1)
       have i₂ := eq12 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op (M.op X1 X0) X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X2 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op (M.op X1 X0) X2) X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X0)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1 X0
       have i₂ := eq24 X0 (M.op X1 X0)
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
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
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq24 X2 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq20 (σ X1) (σ X0)
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 (σ X1) (k (σ X0) (σ X1))
       have j1 := eq20 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 (M.op X1 X0) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq39
    | exact resolve eq39 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
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
  clear eq31
  have eq103 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq48 X0 X0 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq106 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq48 X1 X0 X2
       grind)
    | exact superpose eq48 eq18
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq104 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq104
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq104 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq236 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) ≠ X0 ∨ (M.op X1 (M.op X2 X0)) = (k X0 (M.op X1 (M.op X2 X0))) ∨ (k (M.op X2 X0) X1) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq22 X1 X0 X2
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 (M.op X1 (M.op X2 X0))
       have j1 := eq22 X1 X0 X2
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq417 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
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
  have eq421 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
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
  have eq650 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq200 X0 X1
       grind)
    | exact superpose eq200 eq36
    | (have j0 := eq36 X0 X1
       have j1 := eq200 X0 X1
       grind)
    | exact resolve eq36 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq656 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq650 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq666 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq68
    | (have j0 := eq68 (M.op X0 (σ X1)) (k (τ X0) X1)
       have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq1386 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (τ X1))
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq9
    | (have j1 := eq78 X0 X1
       grind)
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1433 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ (M.op X1 X1)) X0) = (σ (M.op (M.op X1 X1) (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 X1 X1
       have i₂ := eq78 (M.op X1 X1) X0
       grind)
    | exact superpose eq78 eq106
    | (have j1 := eq78 (M.op X1 X1) X0
       grind)
    | exact resolve eq106 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq106
  have eq1462 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = (σ (M.op (M.op X1 X1) (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq2043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq417
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq417
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq417 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2047 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq417
       have i₂ := eq25 y x
       grind)
    | exact superpose eq25 eq417
    | (have j1 := eq25 y x
       grind)
    | exact resolve eq417 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2048 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq417
       have i₂ := eq36 y x
       grind)
    | exact superpose eq36 eq417
    | (have j1 := eq36 y x
       grind)
    | exact resolve eq417 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq417
  have eq2052 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq2048
  have eq2053 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2047
  have eq2057 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq2043
  have eq2086 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X1 (σ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq83
    | (have j0 := eq83 (k X1 (τ (σ X0))) (σ X0)
       have j1 := eq44 (τ (σ X0)) (k X1 (τ (σ X0)))
       grind)
    | exact resolve eq83 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq2099 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2086 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2086
    | (have j0 := eq2086 X0 X1
       grind)
    | exact resolve eq2086 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq2101 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2099 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2099
    | (have j0 := eq2099 X0 X1
       grind)
    | exact resolve eq2099 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq3032 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 X1
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq421
    | (have j0 := eq421 X0 X1
       have j1 := eq20 X1 X0
       grind)
    | exact resolve eq421 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq421
  have eq3955 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2053
  have eq4293 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18 (σ x) (σ x)
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq18
    | exact resolve eq18 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq4725 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq24 (σ x) (σ x)
       have i₂ := eq2052
       grind)
    | exact superpose eq2052 eq24
    | exact resolve eq24 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq4908 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83 x (σ y)
       have i₂ := eq3955
       grind)
    | exact superpose eq3955 eq83
    | (have j0 := eq83 (k x (τ (σ y))) (σ y)
       grind)
    | exact resolve eq83 eq3955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq3955
  have eq4924 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4908
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4908
    | exact resolve eq4908 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4908
  have eq4930 : x = y ∨ y = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4924
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4924
    | exact resolve eq4924 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924
  have eq4931 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq4930
  have eq5143 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25 y x
       have i₂ := eq4931
       grind)
    | exact superpose eq4931 eq25
    | (have j0 := eq25 y x
       grind)
    | exact resolve eq25 eq4931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq5148 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5143
  have eq5359 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq48 x X0 y
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq48
    | exact resolve eq48 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq5148
  have eq17079 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq2102 X1 X0
       grind)
    | exact superpose eq2102 eq18
    | (have j1 := eq2102 X1 X0
       grind)
    | exact resolve eq18 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq18352 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4293
       grind)
    | exact superpose eq4293 eq14
    | exact resolve eq14 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq21108 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0
       have i₂ := eq1386 (τ X0) X1
       grind)
    | exact superpose eq1386 eq63
    | (have j1 := eq1386 (τ X1) X0
       grind)
    | exact resolve eq63 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1386
  have eq21146 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq21108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21108
  have eq21206 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21146 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21146
    | (have j0 := eq21146 X0 X1
       grind)
    | exact resolve eq21146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21146
  have eq21233 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21206 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq21206
    | (have j0 := eq21206 X0 X1
       grind)
    | exact resolve eq21206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21206
  have eq40889 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0
       have i₂ := eq666 (σ X0) X1
       grind)
    | exact superpose eq666 eq732
    | (have j1 := eq666 (σ X1) X0
       grind)
    | exact resolve eq732 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq41086 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40889 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40889
    | (have j0 := eq40889 X0 X1
       grind)
    | exact resolve eq40889 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40889
  have eq41135 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41086 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41086
    | (have j0 := eq41086 X0 X1
       grind)
    | exact resolve eq41086 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41086
  have eq41166 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41135 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq41135
    | (have j0 := eq41135 X0 X1
       grind)
    | exact resolve eq41135 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41135
  have eq41177 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41166 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq41166
    | (have j0 := eq41166 X0 X1
       grind)
    | exact resolve eq41166 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41166
  have eq41178 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq41177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41177
  have eq72559 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0
       have i₂ := eq3032 X0 X1
       grind)
    | exact superpose eq3032 eq732
    | (have j1 := eq3032 X1 X0
       grind)
    | exact resolve eq732 eq3032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq3032
  have eq72756 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq72559 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq72559
    | (have j0 := eq72559 X0 X1
       grind)
    | exact resolve eq72559 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72559
  have eq72757 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq72756 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72756
  have eq72854 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72757 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq72757
    | (have j0 := eq72757 X0 X1
       grind)
    | exact resolve eq72757 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72757
  have eq72855 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq72854 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72854
  have eq86652 : (τ (σ y)) = (k y x) ∨ x = y ∨ x = (k y x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41178 x y
       have i₂ := eq4725
       grind)
    | exact superpose eq4725 eq41178
    | (have j0 := eq41178 x y
       grind)
    | exact resolve eq41178 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4725 eq41178
  have eq86753 : (τ (σ y)) = (k y x) ∨ x = y ∨ x = (k y x) ∨ y = (M.op y x) := by grind
  clear eq86652
  have eq86785 : y = (k y x) ∨ x = y ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq86753
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq86753
    | exact resolve eq86753 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86753
  have eq98222 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq86785
       have i₂ := eq25 x y
       grind)
    | exact superpose eq25 eq86785
    | (have j1 := eq25 x y
       grind)
    | exact resolve eq86785 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq86785
  have eq98288 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq98222
  have eq98409 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18 y x
       have i₂ := eq98288
       grind)
    | exact superpose eq98288 eq18
    | exact resolve eq18 eq98288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98288
  have eq98555 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5359 y
       have i₂ := eq98409
       grind)
    | exact superpose eq98409 eq5359
    | exact resolve eq5359 eq98409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359 eq98409
  have eq98660 : x = (M.op x y) ∨ x = y := by grind
  clear eq98555
  have eq98694 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq18352
       have i₂ := eq98660
       grind)
    | exact superpose eq98660 eq18352
    | exact resolve eq18352 eq98660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18352
  have eq98706 : y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq98660
       grind)
    | exact superpose eq98660 eq18
    | exact resolve eq18 eq98660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98834 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq98694
  have eq98835 : y = (M.op x x) ∨ x = y := by grind
  clear eq98834
  have eq99022 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq72855 x y
       have i₂ := eq98706
       grind)
    | exact superpose eq98706 eq72855
    | (have j0 := eq72855 x y
       grind)
    | exact resolve eq72855 eq98706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72855
  have eq99023 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = y := by grind
  clear eq99022
  have eq99105 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq103 x x
       have i₂ := eq98835
       grind)
    | exact superpose eq98835 eq103
    | exact resolve eq103 eq98835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq98835
  have eq137765 : ∀ X0 X1 X2 : G, X0 ≠ X2 ∨ (k X2 X0) = X0 ∨ (M.op (M.op (M.op X1 X0) X2) X0) = (k (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236 X2 X1 (M.op X0 X1)
       have i₂ := eq39 X0 X1 X2
       grind)
    | exact superpose eq39 eq236
    | (have j0 := eq236 X2 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq236 X1 X1 (M.op X0 X1)
       have r₂ := eq39 X0 X1 X1
       grind)
    | exact resolve eq236 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq236
  have eq137859 : ∀ X0 X1 X2 : G, X0 ≠ X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op (M.op X1 X0) X2) X0) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137765 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq137765
    | (have j0 := eq137765 X0 X1 X2
       grind)
    | (have r₁ := eq137765 (M.op (M.op X1 X0) X2) X1 (M.op (M.op (M.op X1 X0) X2) X0)
       have r₂ := eq29 X0 X1 X2
       grind)
    | (have r₁ := eq137765 (M.op (M.op (M.op X1 X0) X2) X0) X1 (M.op (M.op X1 X0) X2)
       have r₂ := eq29 X0 X1 X2
       grind)
    | exact resolve eq137765 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq137765
  have eq157678 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq99023
       grind)
    | exact superpose eq99023 eq14
    | exact resolve eq14 eq99023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99023
  have eq158297 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq157678
       have i₂ := eq98660
       grind)
    | exact superpose eq98660 eq157678
    | exact resolve eq157678 eq98660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98660 eq157678
  have eq158314 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y := by grind
  clear eq158297
  have eq158315 : x = (k y x) ∨ x = y := by grind
  clear eq158314
  have eq160145 : x = (M.op y x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq99105 x
       have i₂ := eq158315
       grind)
    | exact superpose eq158315 eq99105
    | (have j0 := eq99105 x
       grind)
    | exact resolve eq99105 eq158315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99105 eq158315
  have eq160221 : x = (M.op y x) ∨ x = y := by grind
  clear eq160145
  have eq162561 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq98706
       have i₂ := eq160221
       grind)
    | exact superpose eq160221 eq98706
    | exact resolve eq98706 eq160221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98706 eq160221
  have eq162790 : x = y := by grind
  clear eq162561
  have eq164677 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq162790
       grind)
    | exact superpose eq162790 eq14
    | exact resolve eq14 eq162790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162790
  have eq173151 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq164677
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq164677
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq164677
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq164677
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq164677 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173152 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq164677
       have i₂ := eq656 (σ x) X0
       grind)
    | exact superpose eq656 eq164677
    | (have j1 := eq656 (σ x) X0
       grind)
    | exact resolve eq164677 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201132 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq173151 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173151
  have eq201950 : (τ (M.op (σ x) (σ (M.op x x)))) = (k (τ (σ x)) (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq68 (σ x) (M.op x x)
       have i₂ := eq201132
       grind)
    | exact superpose eq201132 eq68
    | (have j0 := eq68 (M.op (σ x) (σ (M.op x x))) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq68 eq201132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201132
  have eq201952 : (k x (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq201950
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq201950
    | exact resolve eq201950 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201950
  have eq201957 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq201952
  have eq201959 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq201957
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq201957
    | exact resolve eq201957 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201957
  have eq557554 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (k X0 X1))) ∨ (k X0 X1) = X1 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (τ X0) (τ X1)
       have i₂ := eq21233 X1 X0
       grind)
    | exact superpose eq21233 eq18
    | (have j1 := eq21233 X1 X0
       grind)
    | exact resolve eq18 eq21233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq21233
  have eq599537 : ∀ X0 X1 : G, (M.op X0 (τ (k X1 (σ X0)))) = X0 ∨ (σ X0) = (k X1 (σ X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq557554 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq557554
    | (have j0 := eq557554 X1 (σ X0)
       grind)
    | exact resolve eq557554 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557554
  have eq622635 : ∀ X0 X1 : G, (M.op X1 (k (τ X0) X1)) = X1 ∨ (σ X1) = (k X0 (σ X1)) ∨ (τ X0) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq599537 X1 X0
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq599537
    | (have j0 := eq599537 X1 X0
       have j1 := eq68 X0 X1
       grind)
    | exact resolve eq599537 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599537
  have eq622812 : ∀ X0 X1 : G, (M.op X1 (k (τ X0) X1)) = X1 ∨ (σ X1) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq622635 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622635
  have eq623076 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (M.op X1 (k X0 X1)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq622812 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq622812
    | (have j0 := eq622812 (σ X0) X1
       grind)
    | exact resolve eq622812 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622812
  have eq758790 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) X1) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq137859 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137859
  have eq758791 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq758790 X1 X0
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq758790
    | (have j0 := eq758790 X0 X1
       grind)
    | exact resolve eq758790 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758790
  have eq759079 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17079 (M.op X0 X1) X1
       have i₂ := eq758791 X0 X1
       grind)
    | exact superpose eq758791 eq17079
    | (have j0 := eq17079 X1 X1
       have j1 := eq758791 X0 X1
       grind)
    | exact resolve eq17079 eq758791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17079 eq758791
  have eq759127 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq759079 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759079
  have eq760368 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq201959
       have i₂ := eq759127 x x
       grind)
    | exact superpose eq759127 eq201959
    | (have j1 := eq759127 x x
       grind)
    | exact resolve eq201959 eq759127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201959 eq759127
  have eq760439 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq760368
  have eq760451 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq760439
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq760439
    | exact resolve eq760439 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760439
  have eq760452 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq760451
  have eq760528 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq656 x x
       have i₂ := eq760452
       grind)
    | exact superpose eq760452 eq656
    | (have j0 := eq656 x x
       grind)
    | exact resolve eq656 eq760452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq760452
  have eq760545 : x = (M.op x x) := by grind
  clear eq760528
  have eq760621 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq173152 X0
       have i₂ := eq760545
       grind)
    | exact superpose eq760545 eq173152
    | (have j0 := eq173152 X0
       grind)
    | exact resolve eq173152 eq760545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173152
  have eq760751 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq1462 X0 x
       have i₂ := eq760545
       grind)
    | exact superpose eq760545 eq1462
    | exact resolve eq1462 eq760545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq761033 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq760621 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760621
  have eq762960 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq68 X0 x
       have i₂ := eq761033 X0
       grind)
    | exact superpose eq761033 eq68
    | (have j0 := eq68 (M.op X0 (σ x)) (k (τ X0) x)
       grind)
    | exact resolve eq68 eq761033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq763072 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq623076 X0 x
       have i₂ := eq761033 (σ X0)
       grind)
    | exact superpose eq761033 eq623076
    | (have j0 := eq623076 X0 x
       grind)
    | exact resolve eq623076 eq761033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623076 eq761033
  have eq788233 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ (M.op X0 (σ x))) x) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq762960 (M.op X0 (σ x))
       have i₂ := eq24 (σ x) X0
       grind)
    | exact superpose eq24 eq762960
    | (have j0 := eq762960 (M.op X0 (σ x))
       grind)
    | exact resolve eq762960 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762960
  have eq814056 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq24 (σ x) (σ X0)
       have i₂ := eq763072 X0
       grind)
    | exact superpose eq763072 eq24
    | (have j1 := eq763072 X0
       grind)
    | exact resolve eq24 eq763072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq763072
  have eq831497 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq164677
       have i₂ := eq814056 X0
       grind)
    | exact superpose eq814056 eq164677
    | (have j1 := eq814056 X0
       grind)
    | exact resolve eq164677 eq814056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814056
  have eq831667 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq831497 X0
       have i₂ := eq760545
       grind)
    | exact superpose eq760545 eq831497
    | (have j0 := eq831497 X0
       grind)
    | exact resolve eq831497 eq760545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831497
  have eq831668 : ∀ X0 : G, x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq831667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831667
  have eq1002857 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq831668 (τ (M.op X0 (σ x)))
       have i₂ := eq788233 X0
       grind)
    | exact superpose eq788233 eq831668
    | (have j0 := eq831668 (M.op x (τ (M.op X0 (σ x))))
       have j1 := eq788233 X0
       grind)
    | exact resolve eq831668 eq788233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788233 eq831668
  have eq1002858 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq1002857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002857
  have eq1002968 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq760751 (M.op X0 (σ x))
       have i₂ := eq1002858 X0
       grind)
    | exact superpose eq1002858 eq760751
    | (have j0 := eq760751 (M.op X0 (σ x))
       have j1 := eq1002858 X0
       grind)
    | exact resolve eq760751 eq1002858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760751 eq1002858
  have eq1003235 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq1002968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002968
  have eq1003308 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1003235
  have eq1003479 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq1003308
       grind)
    | exact superpose eq1003308 eq10
    | exact resolve eq10 eq1003308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003308
  have eq1003480 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1003479
  have eq1003515 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq164677
       have i₂ := eq1003480
       grind)
    | exact superpose eq1003480 eq164677
    | exact resolve eq164677 eq1003480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164677 eq1003480
  have eq1003972 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1003515
       have i₂ := eq760545
       grind)
    | exact superpose eq760545 eq1003515
    | exact resolve eq1003515 eq760545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760545 eq1003515
  have eq1003973 : False := by grind
  exact eq1003973

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation1246 : Law3.StructuralFromFin Law1246 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V1_Equation1246

/-- `Equation1247`: `x = x ◇ (((y ◇ x) ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V1_Equation1247 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1247 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law1247.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X0) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X2 (M.op (M.op (M.op x (M.op (M.op X0 X1) X2)) x) x)
       have i₂ := eq8 (M.op (M.op X0 X1) X2) x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X3)) = X1 ∨ (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X2 X1) X3
       have i₂ := eq12 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op (M.op X1 X0) X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X2 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 (M.op (M.op x (M.op X0 X1)) x)
       have i₂ := eq18 x (M.op X0 X1) x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X1 X0) X2) X0 X3 X4
       have i₂ := eq18 X1 X0 X2
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X0)
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq28
    | exact resolve eq28 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op X1 X0) X2
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq18
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq20 (σ X1) (σ X0)
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 (σ X1) (k (σ X0) (σ X1))
       have j1 := eq20 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq39 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq63 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq20 X1 (τ X0)
       grind)
    | exact superpose eq20 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq20 X1 (τ X0)
       grind)
    | exact resolve eq33 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq75 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq34
    | (have j0 := eq34 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq101 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq41 X0 X0 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq136 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq102 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq102
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq204 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) X2) (M.op X3 X4)) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X0 (M.op (M.op X0 X1) X2) X1 X3
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq22
    | (have j0 := eq22 X3 (M.op (M.op X1 X0) X2) X2 X4
       grind)
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq373 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq36 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq36 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq433 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq53
    | (have j0 := eq53 X0 X1
       have j1 := eq136 X0 X1
       grind)
    | exact resolve eq53 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq441 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq537 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq67
    | (have j0 := eq67 (M.op X0 (σ X1)) (k (τ X0) X1)
       have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq1467 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1609 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (τ X1))
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq9
    | (have j1 := eq75 X0 X1
       grind)
    | exact resolve eq9 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1666 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X1 X1) X2) ∨ (k (σ (M.op (M.op X1 X1) X2)) X0) = (σ (M.op (M.op (M.op X1 X1) X2) (τ X0))) ∨ (τ X0) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X1 X2 X1 X2
       have i₂ := eq75 (M.op (M.op X1 X1) X2) X0
       grind)
    | exact superpose eq75 eq30
    | (have j1 := eq75 (M.op (M.op X1 X1) X2) X0
       grind)
    | exact resolve eq30 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq75
  have eq1695 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X1 X1) X2)) X0) = (σ (M.op (M.op (M.op X1 X1) X2) (τ X0))) ∨ (τ X0) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1666 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq1918 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq373
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq373
    | (have j1 := eq20 y x
       grind)
    | exact resolve eq373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq373
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq373
    | (have j1 := eq53 y x
       grind)
    | exact resolve eq373 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1921 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq373
       have i₂ := eq441 y x
       grind)
    | exact superpose eq441 eq373
    | (have j1 := eq441 y x
       grind)
    | exact resolve eq373 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq1923 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq1921
  have eq1924 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq1920
  have eq1926 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq1918
  have eq2116 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1 (σ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq80
    | (have j0 := eq80 (k X1 (τ (σ X0))) (σ X0)
       have j1 := eq48 (τ (σ X0)) (k X1 (τ (σ X0)))
       grind)
    | exact resolve eq80 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq2129 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2116 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2116
    | (have j0 := eq2116 X0 X1
       grind)
    | exact resolve eq2116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116
  have eq2131 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2129 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2129
    | (have j0 := eq2129 X0 X1
       grind)
    | exact resolve eq2129 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq2132 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq3499 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq1926
  have eq4203 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    grind
  clear eq204
  have eq4254 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4203 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq4203
    | (have j0 := eq4203 X0 X1 X2
       grind)
    | exact resolve eq4203 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq5306 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq80 x (σ y)
       have i₂ := eq3499
       grind)
    | exact superpose eq3499 eq80
    | (have j0 := eq80 (k x (τ (σ y))) (σ y)
       grind)
    | exact resolve eq80 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq3499
  have eq5317 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq5306
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5306
    | exact resolve eq5306 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306
  have eq5318 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y := by grind
  clear eq5317
  have eq5321 : x = y ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5318
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5318
    | exact resolve eq5318 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5318
  have eq5322 : y = (k x y) ∨ x = y := by grind
  clear eq5321
  have eq5719 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq40 y x
       have i₂ := eq5322
       grind)
    | exact superpose eq5322 eq40
    | (have j0 := eq40 y x
       grind)
    | exact resolve eq40 eq5322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322
  have eq6213 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41 x X0 y
       have i₂ := eq5719
       grind)
    | exact superpose eq5719 eq41
    | exact resolve eq41 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5719
  have eq17954 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 (σ x) (σ x)
       have i₂ := eq1924
       grind)
    | exact superpose eq1924 eq39
    | exact resolve eq39 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq32531 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28 (σ x) (σ x)
       have i₂ := eq1923
       grind)
    | exact superpose eq1923 eq28
    | exact resolve eq28 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq38440 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32531
       grind)
    | exact superpose eq32531 eq14
    | exact resolve eq14 eq32531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32531
  have eq39816 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1467 X0 X1
       grind)
    | exact superpose eq1467 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1467 X0 X1
       grind)
    | exact resolve eq13 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq39878 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39816 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39816
  have eq41150 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) (σ X1)
       have i₂ := eq2132 X1 X0
       grind)
    | exact superpose eq2132 eq28
    | (have j1 := eq2132 X1 X0
       grind)
    | exact resolve eq28 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132
  have eq54539 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0
       have i₂ := eq1609 (τ X0) X1
       grind)
    | exact superpose eq1609 eq62
    | (have j1 := eq1609 (τ X1) X0
       grind)
    | exact resolve eq62 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1609
  have eq54579 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq54539 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54539
  have eq54703 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54579 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54579
    | (have j0 := eq54579 X0 X1
       grind)
    | exact resolve eq54579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54579
  have eq54750 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54703 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq54703
    | (have j0 := eq54703 X0 X1
       grind)
    | exact resolve eq54703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54703
  have eq81485 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0
       have i₂ := eq537 (σ X0) X1
       grind)
    | exact superpose eq537 eq611
    | (have j1 := eq537 (σ X1) X0
       grind)
    | exact resolve eq611 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq81751 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81485 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq81485
    | (have j0 := eq81485 X0 X1
       grind)
    | exact resolve eq81485 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81485
  have eq81804 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81751 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq81751
    | (have j0 := eq81751 X0 X1
       grind)
    | exact resolve eq81751 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81751
  have eq81835 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81804 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq81804
    | (have j0 := eq81804 X0 X1
       grind)
    | exact resolve eq81804 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81804
  have eq81845 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81835 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq81835
    | (have j0 := eq81835 X0 X1
       grind)
    | exact resolve eq81835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81835
  have eq81846 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81845 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81845
  have eq87261 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41150 X0 X1
       have i₂ := eq39878 X0 X1
       grind)
    | exact superpose eq39878 eq41150
    | (have j0 := eq41150 X0 X1
       have j1 := eq39878 X0 X1
       grind)
    | exact resolve eq41150 eq39878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39878
  have eq87577 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87261
  have eq92555 : (τ (σ y)) = (k y x) ∨ x = y ∨ x = (k y x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq81846 x y
       have i₂ := eq17954
       grind)
    | exact superpose eq17954 eq81846
    | (have j0 := eq81846 x y
       grind)
    | exact resolve eq81846 eq17954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17954 eq81846
  have eq92631 : (τ (σ y)) = (k y x) ∨ x = y ∨ x = (k y x) ∨ y = (M.op y x) := by grind
  clear eq92555
  have eq92666 : y = (k y x) ∨ x = y ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq92631
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq92631
    | exact resolve eq92631 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92631
  have eq98626 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4254 X0 X1 (M.op (M.op X0 (M.op X0 X1)) x)
       have i₂ := eq18 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq18 eq4254
    | (have j0 := eq4254 X0 X1 x
       grind)
    | exact resolve eq4254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4254
  have eq98637 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq98626 X1 (M.op X0 X1)
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq98626
    | exact resolve eq98626 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98626
  have eq98921 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41150 (M.op X1 X0) X0
       have i₂ := eq98637 X0 X1
       grind)
    | exact superpose eq98637 eq41150
    | (have j0 := eq41150 X1 X1
       have j1 := eq98637 X1 X1
       grind)
    | exact resolve eq41150 eq98637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41150 eq98637
  have eq98939 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq98921 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98921
  have eq104471 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq92666
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq92666
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq92666 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq92666
  have eq104533 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq104471
  have eq104703 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq104533
       grind)
    | exact superpose eq104533 eq28
    | exact resolve eq28 eq104533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104533
  have eq104867 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6213 y
       have i₂ := eq104703
       grind)
    | exact superpose eq104703 eq6213
    | exact resolve eq6213 eq104703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6213 eq104703
  have eq105011 : x = (M.op x y) ∨ x = y := by grind
  clear eq104867
  have eq105047 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq38440
       have i₂ := eq105011
       grind)
    | exact superpose eq105011 eq38440
    | exact resolve eq38440 eq105011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38440
  have eq105066 : y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq105011
       grind)
    | exact superpose eq105011 eq28
    | exact resolve eq28 eq105011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105225 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq105047
  have eq105226 : y = (M.op y y) ∨ x = y := by grind
  clear eq105225
  have eq105539 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq87577 y x
       have i₂ := eq105066
       grind)
    | exact superpose eq105066 eq87577
    | (have j0 := eq87577 y x
       grind)
    | exact resolve eq87577 eq105066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87577
  have eq105543 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = y := by grind
  clear eq105539
  have eq105643 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq101 y x
       have i₂ := eq105226
       grind)
    | exact superpose eq105226 eq101
    | exact resolve eq101 eq105226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq105226
  have eq121312 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq105543
       grind)
    | exact superpose eq105543 eq14
    | exact resolve eq14 eq105543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105543
  have eq121441 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq121312
       have i₂ := eq105011
       grind)
    | exact superpose eq105011 eq121312
    | exact resolve eq121312 eq105011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105011 eq121312
  have eq121458 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y := by grind
  clear eq121441
  have eq121459 : x = (k y x) ∨ x = y := by grind
  clear eq121458
  have eq121581 : x = (M.op y x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq105643 x
       have i₂ := eq121459
       grind)
    | exact superpose eq121459 eq105643
    | (have j0 := eq105643 x
       grind)
    | exact resolve eq105643 eq121459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105643 eq121459
  have eq121660 : x = (M.op y x) ∨ x = y := by grind
  clear eq121581
  have eq121694 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq105066
       have i₂ := eq121660
       grind)
    | exact superpose eq121660 eq105066
    | exact resolve eq105066 eq121660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105066 eq121660
  have eq122005 : x = y := by grind
  clear eq121694
  have eq122020 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq122005
       grind)
    | exact superpose eq122005 eq14
    | exact resolve eq14 eq122005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122005
  have eq123342 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq122020
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq122020
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq122020
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq122020
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq122020 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123343 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq122020
       have i₂ := eq441 (σ x) X0
       grind)
    | exact superpose eq441 eq122020
    | (have j1 := eq441 (σ x) X0
       grind)
    | exact resolve eq122020 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130098 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq123342 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123342
  have eq130413 : (τ (M.op (σ x) (σ (M.op x x)))) = (k (τ (σ x)) (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq67 (σ x) (M.op x x)
       have i₂ := eq130098
       grind)
    | exact superpose eq130098 eq67
    | (have j0 := eq67 (M.op (σ x) (σ (M.op x x))) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq67 eq130098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130098
  have eq130414 : (k x (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq130413
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq130413
    | exact resolve eq130413 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130413
  have eq130419 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq130414
  have eq130421 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq130419
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq130419
    | exact resolve eq130419 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130419
  have eq237657 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (k X0 X1))) ∨ (k X0 X1) = X1 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) (τ X1)
       have i₂ := eq54750 X1 X0
       grind)
    | exact superpose eq54750 eq28
    | (have j1 := eq54750 X1 X0
       grind)
    | exact resolve eq28 eq54750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq54750
  have eq250301 : ∀ X0 X1 : G, (M.op X0 (τ (k X1 (σ X0)))) = X0 ∨ (σ X0) = (k X1 (σ X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq237657 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq237657
    | (have j0 := eq237657 X1 (σ X0)
       grind)
    | exact resolve eq237657 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237657
  have eq257864 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq130421
       have i₂ := eq98939 x x
       grind)
    | exact superpose eq98939 eq130421
    | (have j1 := eq98939 x x
       grind)
    | exact resolve eq130421 eq98939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98939 eq130421
  have eq257929 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq257864
  have eq257943 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq257929
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq257929
    | exact resolve eq257929 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257929
  have eq257944 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq257943
  have eq258002 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq441 x x
       have i₂ := eq257944
       grind)
    | exact superpose eq257944 eq441
    | (have j0 := eq441 x x
       grind)
    | exact resolve eq441 eq257944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq257944
  have eq258019 : x = (M.op x x) := by grind
  clear eq258002
  have eq258076 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq123343 X0
       have i₂ := eq258019
       grind)
    | exact superpose eq258019 eq123343
    | (have j0 := eq123343 X0
       grind)
    | exact resolve eq123343 eq258019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123343
  have eq258193 : ∀ X0 X1 : G, (k (σ (M.op x X0)) X1) = (σ (M.op (M.op x X0) (τ X1))) ∨ (τ X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1695 X0 x x
       have i₂ := eq258019
       grind)
    | exact superpose eq258019 eq1695
    | exact resolve eq1695 eq258019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq258585 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq258076 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258076
  have eq260764 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq67 X0 x
       have i₂ := eq258585 X0
       grind)
    | exact superpose eq258585 eq67
    | (have j0 := eq67 (M.op X0 (σ x)) (k (τ X0) x)
       grind)
    | exact resolve eq67 eq258585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270128 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ (M.op X0 (σ x))) x) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq260764 (M.op X0 (σ x))
       have i₂ := eq39 (σ x) X0
       grind)
    | exact superpose eq39 eq260764
    | (have j0 := eq260764 (M.op X0 (σ x))
       grind)
    | exact resolve eq260764 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260764
  have eq328473 : ∀ X0 X1 : G, (M.op X1 (k (τ X0) X1)) = X1 ∨ (σ X1) = (k X0 (σ X1)) ∨ (τ X0) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq250301 X1 X0
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq250301
    | (have j0 := eq250301 X1 X0
       have j1 := eq67 X0 X1
       grind)
    | exact resolve eq250301 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250301
  have eq328724 : ∀ X0 X1 : G, (M.op X1 (k (τ X0) X1)) = X1 ∨ (σ X1) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq328473 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328473
  have eq329103 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (M.op X1 (k X0 X1)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq328724 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq328724
    | (have j0 := eq328724 (σ X0) X1
       grind)
    | exact resolve eq328724 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328724
  have eq329426 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq258585 (σ X0)
       have i₂ := eq329103 X0 x
       grind)
    | exact superpose eq329103 eq258585
    | (have j1 := eq329103 X0 x
       grind)
    | exact resolve eq258585 eq329103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258585 eq329103
  have eq331969 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq39 (σ x) (σ X0)
       have i₂ := eq329426 X0
       grind)
    | exact superpose eq329426 eq39
    | (have j1 := eq329426 X0
       grind)
    | exact resolve eq39 eq329426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329426
  have eq332996 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq122020
       have i₂ := eq331969 X0
       grind)
    | exact superpose eq331969 eq122020
    | (have j1 := eq331969 X0
       grind)
    | exact resolve eq122020 eq331969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331969
  have eq333172 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq332996 X0
       have i₂ := eq258019
       grind)
    | exact superpose eq258019 eq332996
    | (have j0 := eq332996 X0
       grind)
    | exact resolve eq332996 eq258019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332996
  have eq333173 : ∀ X0 : G, x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq333172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333172
  have eq373238 : ∀ X0 : G, (σ (M.op x (τ X0))) = (k (σ (M.op x (τ X0))) X0) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq258193 (τ X0) X0
       have i₂ := eq39 (τ X0) x
       grind)
    | exact superpose eq39 eq258193
    | (have j0 := eq258193 (τ X0) X0
       grind)
    | exact resolve eq258193 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq258193
  have eq383743 : ∀ X0 : G, (σ (M.op x X0)) = (k (σ (M.op x X0)) (σ X0)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq373238 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq373238
    | exact resolve eq373238 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373238
  have eq383832 : ∀ X0 : G, (τ (σ (M.op x X0))) = (k (τ (σ (M.op x X0))) X0) ∨ (τ (σ (M.op x X0))) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 (σ (M.op x X0)) X0
       have i₂ := eq383743 X0
       grind)
    | exact superpose eq383743 eq67
    | (have j0 := eq67 (σ (M.op x X0)) (k (τ (σ (M.op x X0))) X0)
       have j1 := eq383743 X0
       grind)
    | exact resolve eq67 eq383743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq383743
  have eq383853 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) ∨ (τ (σ (M.op x X0))) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq383832 X0
       have i₂ := eq9 (M.op x X0)
       grind)
    | exact superpose eq9 eq383832
    | (have j0 := eq383832 X0
       grind)
    | exact resolve eq383832 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383832
  have eq383859 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op x X0) = (k (M.op x X0) X0) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq383853 X0
       have i₂ := eq9 (M.op x X0)
       grind)
    | exact superpose eq9 eq383853
    | (have j0 := eq383853 X0
       grind)
    | exact resolve eq383853 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383853
  have eq383860 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq383859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383859
  have eq388449 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq333173 (τ (M.op X0 (σ x)))
       have i₂ := eq270128 X0
       grind)
    | exact superpose eq270128 eq333173
    | (have j0 := eq333173 (M.op x (τ (M.op X0 (σ x))))
       have j1 := eq270128 X0
       grind)
    | exact resolve eq333173 eq270128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270128 eq333173
  have eq388454 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq388449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388449
  have eq388749 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq383860 (τ (M.op X0 (σ x)))
       have i₂ := eq388454 X0
       grind)
    | exact superpose eq388454 eq383860
    | (have j1 := eq388454 X0
       grind)
    | exact resolve eq383860 eq388454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383860 eq388454
  have eq388874 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq388749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388749
  have eq389014 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq611 x
       have i₂ := eq388874 (σ x)
       grind)
    | exact superpose eq388874 eq611
    | (have j0 := eq611 x
       have j1 := eq388874 (σ x)
       grind)
    | exact resolve eq611 eq388874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq388874
  have eq389022 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq389014
  have eq389153 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq389022
       grind)
    | exact superpose eq389022 eq10
    | exact resolve eq10 eq389022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389022
  have eq389282 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq122020
       have i₂ := eq389153
       grind)
    | exact superpose eq389153 eq122020
    | exact resolve eq122020 eq389153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122020 eq389153
  have eq389737 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq389282
       have i₂ := eq258019
       grind)
    | exact superpose eq258019 eq389282
    | exact resolve eq389282 eq258019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258019 eq389282
  have eq389738 : False := by grind
  exact eq389738

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation1247 : Law3.StructuralFromFin Law1247 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V1_Equation1247

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if X = m(Y,Y) then m(Y,X) else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G1V4_Equation1260 :
    AutBox.GuardFix (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1260 := by
  classical
  refine AutBox.guardFix_of (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X2)) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X1 X2) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq20 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq20 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq38 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq22
    | (have j0 := eq22 X0 (M.op X1 X1)
       have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | (have j1 := eq22 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq43 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq9
    | (have j1 := eq23 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq16
    | exact resolve eq16 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2 x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq63
    | exact resolve eq63 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq83 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X1)) = (M.op X2 (M.op X2 X1)) ∨ (k X0 (M.op X2 X1)) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 X1 (M.op X2 X1)
       have i₂ := eq12 X0 (M.op X2 X1)
       grind)
    | (have i₁ := eq19 X0 X1 X2
       have i₂ := eq12 (M.op (M.op X0 X1) X2) X1
       grind)
    | exact superpose eq12 eq19
    | (have j0 := eq19 X2 X1 (M.op X2 X1)
       have j1 := eq12 X2 (M.op X2 X1)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq140 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | (have j0 := eq25 (σ (k X1 (τ X0))) (M.op (σ X1) X0)
       grind)
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | (have j1 := eq25 X1 X0
       grind)
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq317 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) X2
       have i₂ := eq75 X2 X0 X1
       grind)
    | exact superpose eq75 eq8
    | exact resolve eq8 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq451 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x (M.op X0 X1)
       have i₂ := eq317 x (M.op X0 X1) X0
       grind)
    | exact superpose eq317 eq16
    | exact resolve eq16 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq317
  have eq468 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq476 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X0) X1)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq9
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq9 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq540 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 (M.op X1 X0)
       have i₂ := eq451 X1 X0
       grind)
    | exact superpose eq451 eq451
    | exact resolve eq451 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (M.op X0 X1)
       have i₂ := eq540 X1 X0
       grind)
    | exact superpose eq540 eq32
    | (have j0 := eq32 X1 (M.op X0 X1)
       grind)
    | exact resolve eq32 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq706 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (M.op X0 X1) X1
       have i₂ := eq540 X1 X0
       grind)
    | exact superpose eq540 eq33
    | (have j0 := eq33 (M.op X0 X1) X1
       grind)
    | exact resolve eq33 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq717 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 X1
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq706
    | (have j0 := eq706 X0 X1
       grind)
    | exact resolve eq706 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq720 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq703 X0 X1
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq703
    | (have j0 := eq703 X0 X1
       grind)
    | exact resolve eq703 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq722 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 X1
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq717
    | (have j0 := eq717 X0 X1
       grind)
    | exact resolve eq717 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq723 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq1045 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq9
    | (have j1 := eq140 X0 X1
       grind)
    | exact resolve eq9 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1231 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq722 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq722 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq722
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq722 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq722 X0 (M.op X1 X1)
       have r₂ := eq12 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact resolve eq722 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq468 X0 X1
       grind)
    | exact superpose eq468 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq468 X0 X1
       grind)
    | exact resolve eq13 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq10539 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10390
  have eq10864 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10539 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15057 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15074 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (k (σ (M.op (τ X0) (τ X0))) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (M.op (τ X0) (τ X0)))
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq9
    | (have j1 := eq43 X0
       grind)
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq15156 : ∀ X0 : G, (τ X0) = (τ (k (σ (M.op (τ X0) (τ X0))) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15074 X0
       have i₂ := eq451 (τ X0) (τ X0)
       grind)
    | exact superpose eq451 eq15074
    | (have j0 := eq15074 X0
       grind)
    | exact resolve eq15074 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15074
  have eq15166 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15057 X0
       have i₂ := eq451 X0 X0
       grind)
    | exact superpose eq451 eq15057
    | (have j0 := eq15057 X0
       grind)
    | exact resolve eq15057 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15057
  have eq15230 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15166 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq15166 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq15166
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15166 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166
  have eq15889 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (σ X0)
       have i₂ := eq15230 X1 X0
       grind)
    | exact superpose eq15230 eq51
    | (have j0 := eq51 (k X1 (τ (σ X0))) (σ X0)
       have j1 := eq15230 (τ (σ X0)) (k X1 (τ (σ X0)))
       grind)
    | exact resolve eq51 eq15230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15230
  have eq15918 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15889 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15889
    | (have j0 := eq15889 X0 X1
       grind)
    | exact resolve eq15889 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15889
  have eq15926 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq15918 X0 X1
       have j1 := eq1231 X1 X0
       grind)
    | (have r₁ := eq15918 X1 X1
       have r₂ := eq1231 (k X1 X1) X1
       grind)
    | (have r₁ := eq15918 X0 X1
       have r₂ := eq1231 X0 (k X1 X0)
       grind)
    | (have r₁ := eq15918 X0 X1
       have r₂ := eq1231 (τ (σ X0)) X1
       grind)
    | exact resolve eq15918 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15918
  have eq15936 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15926 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15926
    | (have j0 := eq15926 X0 X1
       grind)
    | exact resolve eq15926 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15926
  have eq15942 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15936 X0 X1
       have j1 := eq1231 X1 X0
       grind)
    | (have r₁ := eq15936 X0 X1
       have r₂ := eq1231 X0 X1
       grind)
    | (have r₁ := eq15936 X1 X0
       have r₂ := eq1231 X0 X1
       grind)
    | (have r₁ := eq15936 X1 X1
       have r₂ := eq1231 (k X1 X1) X1
       grind)
    | exact resolve eq15936 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq15936
  have eq16696 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq16714 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16696 X0
       have i₂ := eq540 X0 X0
       grind)
    | exact superpose eq540 eq16696
    | (have j0 := eq16696 X0
       grind)
    | exact resolve eq16696 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16696
  have eq16715 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16714 X0
       have i₂ := eq451 X0 X0
       grind)
    | exact superpose eq451 eq16714
    | (have j0 := eq16714 X0
       grind)
    | exact resolve eq16714 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16714
  have eq16716 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16715 X0
       have j1 := eq722 X0 X0
       grind)
    | (have r₁ := eq16715 x
       have r₂ := eq722 x x
       grind)
    | exact resolve eq16715 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16715
  have eq16827 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16716 X1
       have i₂ := eq10539 X0 X1
       grind)
    | (have i₁ := eq16716 X0
       have i₂ := eq10539 (M.op X0 X0) X1
       grind)
    | exact superpose eq10539 eq16716
    | (have j1 := eq10539 X0 X1
       grind)
    | exact resolve eq16716 eq10539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16866 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq41 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq16716 (σ X0)
       grind)
    | exact superpose eq16716 eq41
    | (have j0 := eq41 (σ X0) (k (τ (M.op (σ X0) (σ X0))) X0)
       grind)
    | exact resolve eq41 eq16716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16716
  have eq16872 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16866 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16866
    | (have j0 := eq16866 X0
       grind)
    | exact resolve eq16866 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16866
  have eq18457 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq18458 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18457
  have eq25112 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16872 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq16872 X0
       have i₂ := eq12 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq12 eq16872
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq16872 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25113 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16872 X0
       have i₂ := eq154 X0 X1
       grind)
    | (have i₁ := eq16872 X0
       have i₂ := eq154 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq154 eq16872
    | (have j1 := eq154 X1 X0
       grind)
    | exact resolve eq16872 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25113
  have eq27359 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq25177 x y
       grind)
    | exact superpose eq25177 eq14
    | (have j1 := eq25177 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq25177 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq25177 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27454 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq451 (σ X0) (σ X1)
       have i₂ := eq25177 X0 X1
       grind)
    | exact superpose eq25177 eq451
    | (have j1 := eq25177 X0 X1
       grind)
    | exact resolve eq451 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25177
  have eq27504 : y = (k x y) ∨ x = y := by
    first
    | (have j1 := eq16827 x y
       grind)
    | (have r₁ := eq27359
       have r₂ := eq16827 x y
       grind)
    | (have r₁ := eq27359
       have r₂ := eq16827 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq27359
       have r₂ := eq16827 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq27359 eq16827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27359
  have eq28133 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq27504
       grind)
    | exact superpose eq27504 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq27504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27504
  have eq47796 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27454 X0 X1
       have i₂ := eq16827 X0 X1
       grind)
    | exact superpose eq16827 eq27454
    | (have j0 := eq27454 X0 X1
       have j1 := eq16827 X0 X1
       grind)
    | exact resolve eq27454 eq16827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16827
  have eq47974 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47796 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47796
  have eq50046 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47974 (M.op X0 X1) X1
       have i₂ := eq540 X1 X0
       grind)
    | exact superpose eq540 eq47974
    | (have j0 := eq47974 (M.op X0 X1) X1
       grind)
    | exact resolve eq47974 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47974
  have eq50351 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50046 X0 X1
       have j1 := eq722 X0 X1
       grind)
    | (have r₁ := eq50046 X0 X1
       have r₂ := eq722 X0 X1
       grind)
    | exact resolve eq50046 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50046
  have eq51567 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq451 (σ X0) (σ (M.op X1 X0))
       have i₂ := eq50351 X1 X0
       grind)
    | exact superpose eq50351 eq451
    | (have j1 := eq50351 X1 X0
       grind)
    | exact resolve eq451 eq50351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50351
  have eq85936 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25112 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq25112
    | (have j0 := eq25112 (σ X0) X1
       grind)
    | exact resolve eq25112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25112
  have eq88231 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) X1
       have i₂ := eq85936 X0 X1
       grind)
    | exact superpose eq85936 eq41
    | (have j0 := eq41 (M.op (σ X0) (σ X1)) (k (τ (σ X0)) X1)
       have j1 := eq85936 X0 X1
       grind)
    | exact resolve eq41 eq85936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq85936
  have eq88270 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88231 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88231
    | (have j0 := eq88231 X0 X1
       grind)
    | exact resolve eq88231 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88231
  have eq88296 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88270 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88270
    | (have j0 := eq88270 X0 X1
       grind)
    | exact resolve eq88270 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88270
  have eq88297 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq88296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88296
  have eq99441 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (k (σ X0) (σ X1))) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq476 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq476
    | (have j0 := eq476 (k (σ X0) (σ X1)) (M.op X0 X1)
       grind)
    | exact resolve eq476 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq100599 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (k (σ X0) (σ X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq540 X1 X1
       have i₂ := eq99441 X0 X1
       grind)
    | (have i₁ := eq540 X0 X1
       have i₂ := eq99441 (M.op X1 X0) X1
       grind)
    | exact superpose eq99441 eq540
    | (have j1 := eq99441 X0 X1
       grind)
    | exact resolve eq540 eq99441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq99441
  have eq102810 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (τ X1) = X0 ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq1045 X1 X0
       grind)
    | exact superpose eq1045 eq23
    | (have j0 := eq23 X1 X0
       have j1 := eq1045 X1 X0
       grind)
    | exact resolve eq23 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1045
  have eq103034 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq102810 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102810
  have eq104471 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15156 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15156
    | exact resolve eq15156 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15156
  have eq113368 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k (M.op X0 X1) X1) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88297 (M.op X0 X1) X1
       have i₂ := eq51567 X1 X0
       grind)
    | exact superpose eq51567 eq88297
    | (have j0 := eq88297 (M.op X0 X1) X1
       have j1 := eq51567 X1 X0
       grind)
    | exact resolve eq88297 eq51567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51567 eq88297
  have eq113435 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq113368 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113368
  have eq113461 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (τ (σ (M.op X0 X1))) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq113435 X0 X1
       have j1 := eq722 X0 X1
       grind)
    | (have r₁ := eq113435 X0 X1
       have r₂ := eq722 X0 X1
       grind)
    | exact resolve eq113435 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq113435
  have eq113469 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq113461 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq113461
    | (have j0 := eq113461 X0 X1
       grind)
    | exact resolve eq113461 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113461
  have eq113698 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq113469 X1 (M.op X0 X1)
       have i₂ := eq451 X0 X1
       grind)
    | exact superpose eq451 eq113469
    | exact resolve eq113469 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113469
  have eq113960 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18458 X0 X0
       have i₂ := eq113698 X0 X0
       grind)
    | exact superpose eq113698 eq18458
    | (have j0 := eq18458 X0 X0
       have j1 := eq113698 X0 X0
       grind)
    | exact resolve eq18458 eq113698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18458 eq113698
  have eq113977 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq113960 X0
       have j1 := eq723 X0 X0
       grind)
    | (have r₁ := eq113960 X0
       have r₂ := eq723 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq113960 x
       have r₂ := eq723 x x
       grind)
    | exact resolve eq113960 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113960
  have eq113985 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq113977 X0
       have i₂ := eq451 X0 X0
       grind)
    | exact superpose eq451 eq113977
    | (have j0 := eq113977 X0
       grind)
    | exact resolve eq113977 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113977
  have eq113989 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq113985 X0
       have j1 := eq723 X0 X0
       grind)
    | (have r₁ := eq113985 x
       have r₂ := eq723 x x
       grind)
    | exact resolve eq113985 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq113985
  have eq114010 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq113989 X1
       have i₂ := eq10539 X0 X1
       grind)
    | (have i₁ := eq113989 X0
       have i₂ := eq10539 (M.op X0 X0) X1
       grind)
    | exact superpose eq10539 eq113989
    | (have j1 := eq10539 X0 X1
       grind)
    | exact resolve eq113989 eq10539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10539
  have eq114031 : y = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq113989 y
       have i₂ := eq28133
       grind)
    | exact superpose eq28133 eq113989
    | exact resolve eq113989 eq28133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28133
  have eq114083 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27454 X0 (M.op X0 X0)
       have i₂ := eq113989 X0
       grind)
    | exact superpose eq113989 eq27454
    | (have j0 := eq27454 (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact resolve eq27454 eq113989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114088 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq113989 (σ X0)
       grind)
    | exact superpose eq113989 eq51
    | (have j0 := eq51 (k X0 (τ (M.op (σ X0) (σ X0)))) (σ X0)
       grind)
    | exact resolve eq51 eq113989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq113989
  have eq114093 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq114083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114083
  have eq114103 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq114088 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114088
    | (have j0 := eq114088 X0
       grind)
    | exact resolve eq114088 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114088
  have eq114606 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq27454 y x
       have i₂ := eq114031
       grind)
    | exact superpose eq114031 eq27454
    | (have j0 := eq27454 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq27454 eq114031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27454 eq114031
  have eq114614 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq114606
  have eq114671 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114614
       grind)
    | exact superpose eq114614 eq14
    | exact resolve eq14 eq114614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114614
  have eq117254 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114103 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114103
    | exact resolve eq114103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117270 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114103 X0
       have i₂ := eq154 X0 X1
       grind)
    | (have i₁ := eq114103 X0
       have i₂ := eq154 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq154 eq114103
    | (have j1 := eq154 X1 X0
       grind)
    | exact resolve eq114103 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq114103
  have eq117286 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq117270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117270
  have eq117368 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15942 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq117254 X0
       grind)
    | exact superpose eq117254 eq15942
    | (have j1 := eq117254 X0
       grind)
    | exact resolve eq15942 eq117254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117254
  have eq117369 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq117368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117368
  have eq117497 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq451 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq117369 X0
       grind)
    | exact superpose eq117369 eq451
    | (have j1 := eq117369 X0
       grind)
    | exact resolve eq451 eq117369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117369
  have eq118340 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq117286 x y
       grind)
    | exact superpose eq117286 eq14
    | (have j1 := eq117286 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq117286 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq117286 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq117286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117286
  have eq118443 : y = (k y x) ∨ x = y := by
    first
    | (have j1 := eq114010 x y
       grind)
    | (have r₁ := eq118340
       have r₂ := eq114010 x y
       grind)
    | (have r₁ := eq118340
       have r₂ := eq114010 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq118340
       have r₂ := eq114010 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq118340 eq114010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114010 eq118340
  have eq118539 : y = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq15942 x y
       have i₂ := eq118443
       grind)
    | exact superpose eq118443 eq15942
    | exact resolve eq15942 eq118443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15942 eq118443
  have eq118564 : y = (M.op y x) ∨ x = y := by grind
  clear eq118539
  have eq118728 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq451 y x
       have i₂ := eq118564
       grind)
    | exact superpose eq118564 eq451
    | exact resolve eq451 eq118564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118564
  have eq119080 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq114671
       have i₂ := eq118728
       grind)
    | exact superpose eq118728 eq114671
    | exact resolve eq114671 eq118728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114671 eq118728
  have eq119277 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq119080
  have eq119278 : x = y := by grind
  clear eq119277
  have eq119452 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq119278
       grind)
    | exact superpose eq119278 eq14
    | exact resolve eq14 eq119278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119278
  have eq120010 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq119452
       have i₂ := eq12 X0 (σ x)
       grind)
    | (have i₁ := eq119452
       have i₂ := eq12 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq12 eq119452
    | (have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq119452
       have r₂ := eq12 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq119452 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122820 : (k (σ (M.op x x)) (σ x)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have j0 := eq120010 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120010
  have eq122935 : x = (τ (M.op (σ (M.op x x)) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq104471 x
       have i₂ := eq122820
       grind)
    | exact superpose eq122820 eq104471
    | (have j0 := eq104471 x
       grind)
    | exact resolve eq104471 eq122820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104471 eq122820
  have eq122997 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq122935
       have i₂ := eq114093 x
       grind)
    | exact superpose eq114093 eq122935
    | (have j1 := eq114093 x
       grind)
    | exact resolve eq122935 eq114093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114093 eq122935
  have eq123045 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) := by grind
  clear eq122997
  have eq123059 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq123045
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq123045
    | exact resolve eq123045 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123045
  have eq123060 : x = (M.op x x) := by grind
  clear eq123059
  have eq123107 : ∀ X0 : G, x ≠ x ∨ (σ (k X0 x)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq10864 X0 x
       have i₂ := eq123060
       grind)
    | exact superpose eq123060 eq10864
    | (have j0 := eq10864 X0 x
       grind)
    | (have r₁ := eq10864 X0 x
       have r₂ := eq123060
       grind)
    | exact resolve eq10864 eq123060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10864
  have eq123348 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq123107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123107
  have eq124222 : ∀ X0 : G, (k X0 x) = (τ (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 x)
       have i₂ := eq123348 X0
       grind)
    | exact superpose eq123348 eq9
    | (have j1 := eq123348 X0
       grind)
    | exact resolve eq9 eq123348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123348
  have eq124304 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq124222 X0
       have i₂ := eq9 (M.op X0 x)
       grind)
    | exact superpose eq9 eq124222
    | (have j0 := eq124222 X0
       grind)
    | exact resolve eq124222 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124222
  have eq124389 : x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16872 x
       have i₂ := eq124304 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq124304 eq16872
    | (have j0 := eq16872 x
       have j1 := eq124304 (M.op (τ (M.op (σ x) (σ x))) x)
       grind)
    | exact resolve eq16872 eq124304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16872 eq124304
  have eq124400 : x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq124389
  have eq149890 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq117497 X1
       have i₂ := eq103034 X0 X1
       grind)
    | (have i₁ := eq117497 X0
       have i₂ := eq103034 (τ (M.op X0 X0)) X1
       grind)
    | exact superpose eq103034 eq117497
    | (have j1 := eq103034 X0 X1
       grind)
    | exact resolve eq117497 eq103034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103034 eq117497
  have eq149959 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq149890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149890
  have eq152459 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (τ (σ X1)) = X0 ∨ (M.op X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100599 X0 X1
       have i₂ := eq149959 X0 (σ X1)
       grind)
    | exact superpose eq149959 eq100599
    | (have j0 := eq100599 X0 X1
       have j1 := eq149959 X0 (σ X1)
       grind)
    | exact resolve eq100599 eq149959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100599 eq149959
  have eq152492 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq152459 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq152459
    | (have j0 := eq152459 X0 X1
       grind)
    | exact resolve eq152459 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152459
  have eq152493 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq152492 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152492
  have eq152520 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq152493 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq152493
    | (have j0 := eq152493 X0 X1
       grind)
    | exact resolve eq152493 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152493
  have eq152521 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq152520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152520
  have eq152549 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152521 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152521
    | (have j0 := eq152521 (M.op X1 (τ X0)) (τ (M.op (σ X1) X0))
       grind)
    | exact resolve eq152521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152521
  have eq210057 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 (τ (M.op X1 (σ X0)))) ∨ (τ (M.op X1 (σ X0))) = X0 ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq152549 (M.op X1 (σ X0)) X0
       have i₂ := eq451 X1 (σ X0)
       grind)
    | exact superpose eq451 eq152549
    | (have j0 := eq152549 (M.op X1 (σ X0)) X0
       grind)
    | exact resolve eq152549 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152549
  have eq210065 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (τ (M.op X1 (σ X0))) = X0 ∨ (M.op X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq210057 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq210057
    | (have j0 := eq210057 X0 X1
       grind)
    | exact resolve eq210057 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210057
  have eq210066 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (τ (M.op X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq210065 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210065
  have eq210215 : ∀ X0 X1 : G, (τ (M.op X1 (σ X0))) = (M.op (τ (M.op X1 (σ X0))) X0) ∨ (τ (M.op X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 (τ (M.op X1 (σ X0)))
       have i₂ := eq210066 X0 X1
       grind)
    | exact superpose eq210066 eq451
    | (have j1 := eq210066 X0 X1
       grind)
    | exact resolve eq451 eq210066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq210066
  have eq216747 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq124400
       have i₂ := eq210215 x (σ x)
       grind)
    | exact superpose eq210215 eq124400
    | (have j1 := eq210215 x (σ x)
       grind)
    | exact resolve eq124400 eq210215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124400 eq210215
  have eq216780 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq216747
  have eq216937 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq216780
       grind)
    | exact superpose eq216780 eq10
    | exact resolve eq10 eq216780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216780
  have eq217108 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq119452
       have i₂ := eq216937
       grind)
    | exact superpose eq216937 eq119452
    | exact resolve eq119452 eq216937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119452 eq216937
  have eq217561 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq217108
       have i₂ := eq123060
       grind)
    | exact superpose eq123060 eq217108
    | exact resolve eq217108 eq123060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123060 eq217108
  have eq217562 : False := by grind
  exact eq217562

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation1260 : Law3.StructuralFromFin Law1260 :=
  AutBox.structuralFromFin_boxIte (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G1V4_Equation1260

/-- `Equation1261`: `x = x ◇ (((y ◇ z) ◇ x) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if X = m(Y,Y) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G1V1_Equation1261 :
    AutBox.GuardFix (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1261 := by
  classical
  refine AutBox.guardFix_of (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law1261.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 X5 : G, (M.op X1 (M.op (M.op X0 X1) X5)) = X1 := by
    intro X0 X1 X5
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op (M.op x x) X0) x) X5
       have i₂ := eq8 X0 x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op (M.op x (M.op X0 X1)) x)
       have i₂ := eq16 x (M.op X0 X1) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X0)
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq28
    | exact resolve eq28 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X1 X0) X2
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq16
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq39 X0 X1
       have i₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq78 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq20 (σ X0) (σ X1)
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 (σ X1) (k (σ X0) (σ X1))
       have j1 := eq20 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (M.op X1 X0)
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq79
    | (have j0 := eq79 X1 X0
       grind)
    | exact resolve eq79 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq20 (τ X0) X1
       grind)
    | exact superpose eq20 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq20 (τ X0) X1
       grind)
    | exact resolve eq33 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq89 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq33
    | (have j0 := eq33 X0 (M.op X1 X1)
       have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq112 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq41 X0 X0 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op X1 X2) X3
       have i₂ := eq41 X1 X0 X2
       grind)
    | exact superpose eq41 eq16
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq41
  have eq128 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq184 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq113 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq113
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq113 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq287 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq36 X2 X0
       grind)
    | exact superpose eq36 eq13
    | (have j0 := eq13 (σ (k X1 X2)) (k (σ X1) (M.op (σ X0) (σ X0)))
       have j1 := eq36 X2 X0
       grind)
    | exact resolve eq13 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq528 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X0
       have i₂ := eq184 X0 X1
       grind)
    | exact superpose eq184 eq66
    | (have j0 := eq66 X0 X1
       have j1 := eq184 X0 X1
       grind)
    | exact resolve eq66 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq535 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq528 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq545 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq546 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq92
    | (have j0 := eq92 (M.op X0 (σ X1)) (k (τ X0) X1)
       have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq559 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq545 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq545
    | (have j0 := eq545 X0
       grind)
    | exact resolve eq545 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq614 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq128
    | (have j0 := eq128 (k X0 (τ X1)) (M.op (σ X0) X1)
       have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq128 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = (k (τ X0) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (M.op X1 (τ X0))
       have i₂ := eq28 X1 (τ X0)
       grind)
    | exact superpose eq28 eq88
    | (have j0 := eq88 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq88 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1203 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (M.op X1 (τ X0)) = (k (τ X0) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1188 X0 X1
       have j1 := eq84 (τ X0) X1
       grind)
    | (have r₁ := eq1188 X0 X1
       have r₂ := eq84 (τ X0) X1
       grind)
    | exact resolve eq1188 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1210 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (k (τ X0) (M.op X1 (τ X0))) ∨ (k X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1203
    | (have j0 := eq1203 X0 X1
       grind)
    | exact resolve eq1203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1297 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq89
    | exact resolve eq89 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1900 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X1 (σ X0)
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq128
    | (have j0 := eq128 (k X1 (τ (σ X0))) (σ X0)
       have j1 := eq78 (τ (σ X0)) (k X1 (τ (σ X0)))
       grind)
    | exact resolve eq128 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1913 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1900 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1900
    | (have j0 := eq1900 X0 X1
       grind)
    | exact resolve eq1900 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1915 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1913 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1913
    | (have j0 := eq1913 X0 X1
       grind)
    | exact resolve eq1913 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq1916 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1915 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq8485 : ∀ X0 X1 X2 : G, (k X0 X2) = (τ (k (σ X0) (M.op (σ X1) (σ X1)))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ X0 = X2 ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (k X0 X2)
       have i₂ := eq287 X1 X0 X2
       grind)
    | exact superpose eq287 eq9
    | (have j1 := eq287 X1 X0 X2
       grind)
    | exact resolve eq9 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq15621 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1180 X0 X1
       grind)
    | exact superpose eq1180 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1180 X0 X1
       grind)
    | exact resolve eq13 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq15655 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15621
  have eq17073 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1297 X0 X1
       grind)
    | exact superpose eq1297 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1297 X0 X1
       grind)
    | exact resolve eq13 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq17348 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17073 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17073
  have eq19811 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq1916 y x
       grind)
    | exact superpose eq1916 eq14
    | (have j1 := eq1916 y x
       grind)
    | (have r₁ := eq14
       have r₂ := eq1916 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq1916 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19825 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) (σ X1)
       have i₂ := eq1916 X1 X0
       grind)
    | exact superpose eq1916 eq28
    | (have j1 := eq1916 X1 X0
       grind)
    | exact resolve eq28 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916
  have eq19902 : y = (k x y) ∨ x = y := by
    first
    | (have j1 := eq15655 x y
       grind)
    | (have r₁ := eq19811
       have r₂ := eq15655 x y
       grind)
    | (have r₁ := eq19811
       have r₂ := eq15655 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq19811
       have r₂ := eq15655 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq19811 eq15655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655 eq19811
  have eq19912 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19902
       grind)
    | exact superpose eq19902 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19902
  have eq21732 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (τ (σ X0)) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0
       have i₂ := eq614 X0 (σ X0)
       grind)
    | exact superpose eq614 eq559
    | (have j1 := eq614 X0 (σ X1)
       grind)
    | exact resolve eq559 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq614
  have eq21745 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (τ (σ X0)) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21732 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21732
    | (have j0 := eq21732 X0 X1
       grind)
    | exact resolve eq21732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21732
  have eq21823 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21745 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21745
    | (have j0 := eq21745 X0 X1
       grind)
    | exact resolve eq21745 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21745
  have eq21855 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21823 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq21823
    | (have j0 := eq21823 X0 X1
       grind)
    | exact resolve eq21823 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21823
  have eq21857 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21855 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq21855
    | (have j0 := eq21855 X0 X1
       grind)
    | exact resolve eq21855 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21855
  have eq21858 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21857
  have eq29820 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq112 (τ X0) (τ X0)
       have i₂ := eq1210 X0 (τ X0)
       grind)
    | exact superpose eq1210 eq112
    | (have j0 := eq112 (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0)))
       have j1 := eq1210 X0 (τ X0)
       grind)
    | exact resolve eq112 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29866 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29820 X0
       have i₂ := eq28 (τ X0) (τ X0)
       grind)
    | exact superpose eq28 eq29820
    | (have j0 := eq29820 X0
       grind)
    | exact resolve eq29820 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29820
  have eq29867 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq29866 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29866
  have eq57630 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29867 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29867
    | exact resolve eq29867 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57780 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq128 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq29867 (σ X0)
       grind)
    | exact superpose eq29867 eq128
    | (have j0 := eq128 (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) (σ X0)
       have j1 := eq29867 (σ X0)
       grind)
    | exact resolve eq128 eq29867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29867
  have eq57846 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57780 X0
       have i₂ := eq9 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq57780
    | (have j0 := eq57780 X0
       grind)
    | exact resolve eq57780 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57780
  have eq57891 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57846 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57846
    | (have j0 := eq57846 X0
       grind)
    | exact resolve eq57846 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57846
  have eq57913 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57891 X0
       have i₂ := eq9 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq57891
    | (have j0 := eq57891 X0
       grind)
    | exact resolve eq57891 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57891
  have eq57933 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57913 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57913
    | (have j0 := eq57913 X0
       grind)
    | exact resolve eq57913 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57913
  have eq57952 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq57933 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57933
    | (have j0 := eq57933 X0
       grind)
    | exact resolve eq57933 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57933
  have eq57953 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq57952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57952
  have eq58660 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57953 X1
       have i₂ := eq17348 X0 X1
       grind)
    | (have i₁ := eq57953 X0
       have i₂ := eq17348 (M.op X0 X0) X1
       grind)
    | exact superpose eq17348 eq57953
    | (have j1 := eq17348 X0 X1
       grind)
    | exact resolve eq57953 eq17348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17348
  have eq58676 : y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq57953 y
       have i₂ := eq19912
       grind)
    | exact superpose eq19912 eq57953
    | exact resolve eq57953 eq19912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19912
  have eq58775 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19825 X0 (M.op X0 X0)
       have i₂ := eq57953 X0
       grind)
    | exact superpose eq57953 eq19825
    | (have j0 := eq19825 (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (σ X0))
       have j1 := eq57953 X0
       grind)
    | exact resolve eq19825 eq57953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58820 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq58775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58775
  have eq58858 : y = (k y x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq58676
  have eq58862 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58660 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58660
  have eq59122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19825 y x
       have i₂ := eq58858
       grind)
    | exact superpose eq58858 eq19825
    | (have j0 := eq19825 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq19825 eq58858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19825 eq58858
  have eq59128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq59122
  have eq60614 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq57630 X0
       grind)
    | exact superpose eq57630 eq66
    | (have j0 := eq66 (σ X0) (σ (M.op X0 X0))
       have j1 := eq57630 X0
       grind)
    | exact resolve eq66 eq57630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57630
  have eq60657 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq60614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60614
  have eq63005 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21858 X0 (M.op X0 X0)
       have i₂ := eq60657 X0
       grind)
    | exact superpose eq60657 eq21858
    | (have j0 := eq21858 (τ (σ X0)) (k X0 (M.op X0 X0))
       have j1 := eq60657 X0
       grind)
    | exact resolve eq21858 eq60657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21858 eq60657
  have eq63136 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq63005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63005
  have eq63166 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq63136 X0
       have j1 := eq84 X0 X0
       grind)
    | (have r₁ := eq63136 X0
       have r₂ := eq84 X0 X0
       grind)
    | exact resolve eq63136 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq63136
  have eq63180 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq63166 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63166
    | (have j0 := eq63166 X0
       grind)
    | exact resolve eq63166 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63166
  have eq65489 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq59128
       grind)
    | exact superpose eq59128 eq14
    | exact resolve eq14 eq59128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59128
  have eq67261 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq63180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63180
  have eq67317 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq67261 X0
       have j1 := eq57953 X0
       grind)
    | (have r₁ := eq67261 X0
       have r₂ := eq57953 X0
       grind)
    | exact resolve eq67261 eq57953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57953 eq67261
  have eq70826 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k (τ (σ (M.op X0 X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq546 (σ (M.op X0 X0)) X0
       have i₂ := eq58820 X0
       grind)
    | exact superpose eq58820 eq546
    | (have j0 := eq546 (σ (M.op X0 X0)) X0
       have j1 := eq58820 X0
       grind)
    | exact resolve eq546 eq58820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq58820
  have eq70985 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq70826 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq70826
    | (have j0 := eq70826 X0
       grind)
    | exact resolve eq70826 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70826
  have eq71024 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq70985
  have eq71025 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq71024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71024
  have eq71030 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71025 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq71025
    | (have j0 := eq71025 X0
       grind)
    | exact resolve eq71025 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71025
  have eq71031 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq71030 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71030
  have eq126174 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8485 X0 X0 X1
       have i₂ := eq67317 (σ X0)
       grind)
    | exact superpose eq67317 eq8485
    | (have j0 := eq8485 X0 X0 X1
       grind)
    | exact resolve eq8485 eq67317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8485 eq67317
  have eq126910 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq126174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126174
  have eq126920 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126910 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq126910
    | (have j0 := eq126910 X0 X1
       grind)
    | exact resolve eq126910 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126910
  have eq131746 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq126920 y x
       grind)
    | exact superpose eq126920 eq14
    | (have j1 := eq126920 y x
       grind)
    | (have r₁ := eq14
       have r₂ := eq126920 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq126920 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq126920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126920
  have eq131839 : y = (k y x) ∨ x = y := by
    first
    | (have j1 := eq58862 x y
       grind)
    | (have r₁ := eq131746
       have r₂ := eq58862 x y
       grind)
    | (have r₁ := eq131746
       have r₂ := eq58862 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq131746
       have r₂ := eq58862 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq131746 eq58862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58862 eq131746
  have eq133037 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq66 y x
       have i₂ := eq131839
       grind)
    | exact superpose eq131839 eq66
    | (have j0 := eq66 y x
       grind)
    | exact resolve eq66 eq131839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131839
  have eq133105 : y = (M.op y x) ∨ x = y := by grind
  clear eq133037
  have eq134327 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq133105
       grind)
    | exact superpose eq133105 eq28
    | exact resolve eq28 eq133105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133105
  have eq135096 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq65489
       have i₂ := eq134327
       grind)
    | exact superpose eq134327 eq65489
    | exact resolve eq65489 eq134327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65489 eq134327
  have eq135256 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq135096
  have eq135257 : x = y := by grind
  clear eq135256
  have eq136391 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq135257
       grind)
    | exact superpose eq135257 eq14
    | exact resolve eq14 eq135257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135257
  have eq142716 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq136391
       have i₂ := eq71031 x
       grind)
    | exact superpose eq71031 eq136391
    | (have j1 := eq71031 x
       grind)
    | (have r₁ := eq136391
       have r₂ := eq71031 x
       grind)
    | exact resolve eq136391 eq71031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71031
  have eq142718 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq136391
       have i₂ := eq535 (σ x) X0
       grind)
    | exact superpose eq535 eq136391
    | (have j1 := eq535 (σ x) X0
       grind)
    | exact resolve eq136391 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq142720 : x = (M.op x x) := by grind
  clear eq142716
  have eq143189 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 x x X0 X1
       have i₂ := eq142720
       grind)
    | exact superpose eq142720 eq115
    | exact resolve eq115 eq142720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq152325 : ∀ X0 X1 : G, (k X1 (M.op x X0)) = (M.op X1 (M.op x X0)) ∨ (M.op x X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq112 (M.op x X1) X1
       have i₂ := eq143189 X1 X1
       grind)
    | exact superpose eq143189 eq112
    | exact resolve eq112 eq143189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq143189
  have eq217418 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq142718 X0
       have i₂ := eq142720
       grind)
    | exact superpose eq142720 eq142718
    | (have j0 := eq142718 X0
       grind)
    | exact resolve eq142718 eq142720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142718
  have eq217421 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq217418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217418
  have eq218906 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq128 x X0
       have i₂ := eq217421 X0
       grind)
    | exact superpose eq217421 eq128
    | (have j0 := eq128 (k x (τ X0)) (M.op (σ x) X0)
       grind)
    | exact resolve eq128 eq217421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq217421
  have eq225159 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq218906 (M.op X0 (σ x))
       have i₂ := eq28 X0 (σ x)
       grind)
    | exact superpose eq28 eq218906
    | (have j0 := eq218906 (M.op X0 (σ x))
       grind)
    | exact resolve eq218906 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218906
  have eq225212 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq225159 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq225159
    | (have j0 := eq225159 X0
       grind)
    | exact resolve eq225159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225159
  have eq267906 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ X0) (M.op x (τ X0))) ∨ (k X0 (σ (M.op x (τ X0)))) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1210 X0 x
       have i₂ := eq152325 (τ X0) (τ X0)
       grind)
    | exact superpose eq152325 eq1210
    | (have j0 := eq1210 X0 x
       have j1 := eq152325 (τ X0) (M.op (τ X0) (M.op x (τ X0)))
       grind)
    | exact resolve eq1210 eq152325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210 eq152325
  have eq267935 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (k X0 (σ (M.op x (τ X0)))) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq267906 X0
       have i₂ := eq28 x (τ X0)
       grind)
    | exact superpose eq28 eq267906
    | (have j0 := eq267906 X0
       grind)
    | exact resolve eq267906 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq267906
  have eq267936 : ∀ X0 : G, (k X0 (σ (M.op x (τ X0)))) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq267935 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267935
  have eq272901 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq66 x (τ (M.op X0 (σ x)))
       have i₂ := eq225212 X0
       grind)
    | exact superpose eq225212 eq66
    | (have j0 := eq66 x (τ (M.op X0 (σ x)))
       have j1 := eq225212 X0
       grind)
    | exact resolve eq66 eq225212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq225212
  have eq272911 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq272901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272901
  have eq292060 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (σ x)) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq267936 (M.op X0 (σ x))
       have i₂ := eq272911 X0
       grind)
    | exact superpose eq272911 eq267936
    | (have j1 := eq272911 X0
       grind)
    | exact resolve eq267936 eq272911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267936 eq272911
  have eq292204 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (σ x)) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq292060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292060
  have eq2071381 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq292204
  have eq2071416 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq2071381
       grind)
    | exact superpose eq2071381 eq10
    | exact resolve eq10 eq2071381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071381
  have eq2071417 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2071416
  have eq2071432 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq136391
       have i₂ := eq2071417
       grind)
    | exact superpose eq2071417 eq136391
    | exact resolve eq136391 eq2071417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136391 eq2071417
  have eq2071983 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2071432
       have i₂ := eq142720
       grind)
    | exact superpose eq142720 eq2071432
    | exact resolve eq2071432 eq142720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142720 eq2071432
  have eq2071984 : False := by grind
  exact eq2071984

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation1261 : Law3.StructuralFromFin Law1261 :=
  AutBox.structuralFromFin_boxIte (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G1V1_Equation1261

/-- `Equation2322`: `x = (y ◇ (x ◇ (z ◇ w))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then m(Y,X) else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V4_Equation2322 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2322 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law2322.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op X2 X3))) X0) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 (M.op x (M.op X0 (M.op x x))) X0
       have i₂ := eq8 X0 x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op x (M.op (M.op X0 X1) x)) X0
       have i₂ := eq16 x x (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X2)
       have i₂ := eq22 X0 X2
       grind)
    | exact superpose eq22 eq16
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq22 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
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
  have eq59 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
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
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29 (M.op X1 (M.op X2 X0)) X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq29
    | exact resolve eq29 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq105 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op X2 X0) (M.op X0 X1)
       have i₂ := eq29 X0 X2 X1
       grind)
    | exact superpose eq29 eq22
    | exact resolve eq22 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq29 X0 X0 X0
       grind)
    | exact superpose eq29 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq29 X0 X0 X0
       grind)
    | exact superpose eq29 eq108
    | exact resolve eq108 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq117 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq9
    | (have j1 := eq58 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq135 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = X2 ∨ (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X2 (M.op X2 X3) X3 X1
       have i₂ := eq12 (M.op X2 X3) X0
       grind)
    | (have i₁ := eq91 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq12 eq91
    | (have j1 := eq12 (M.op X2 X3) X0
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq158 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ X0) X1) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq59
    | (have j0 := eq59 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq9
    | (have j1 := eq59 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq222 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq109 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq109
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq288 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq14
    | (have j1 := eq61 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq61 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq61 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq9
    | (have j1 := eq61 X0 X1
       grind)
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq396 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X0
       have i₂ := eq222 X0 X1
       grind)
    | exact superpose eq222 eq66
    | (have j0 := eq66 X0 X1
       have j1 := eq222 X0 X1
       grind)
    | exact resolve eq66 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq403 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq396 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq740 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq117
    | (have j0 := eq117 (M.op X0 (σ X1)) (k (τ X0) X1)
       have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq117 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  clear eq163
  have eq799 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq779 X0
       have i₂ := eq22 (σ X0) (σ X0)
       grind)
    | exact superpose eq22 eq779
    | (have j0 := eq779 X0
       grind)
    | exact resolve eq779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq801 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq799
    | (have j0 := eq799 X0
       grind)
    | exact resolve eq799 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq1424 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (σ (M.op (M.op X1 X1) (τ X0))) = (k (σ (M.op X1 X1)) X0) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 X1 X1
       have i₂ := eq158 (M.op X1 X1) X0
       grind)
    | exact superpose eq158 eq105
    | (have j1 := eq158 (M.op X1 X1) X0
       grind)
    | exact resolve eq105 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq158
  have eq1441 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X1) (τ X0))) = (k (σ (M.op X1 X1)) X0) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq1663 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq288
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq288
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq288 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq288
       have i₂ := eq35 y x
       grind)
    | exact superpose eq35 eq288
    | (have j1 := eq35 y x
       grind)
    | exact resolve eq288 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq288
  have eq1673 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq1666
  have eq1676 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq1663
  have eq5754 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq22 (σ x) (σ x)
       have i₂ := eq1673
       grind)
    | exact superpose eq1673 eq22
    | exact resolve eq22 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq17902 : x = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq801 x
       have i₂ := eq1676
       grind)
    | exact superpose eq1676 eq801
    | exact resolve eq801 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq17910 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0
       have i₂ := eq300 X0 X1
       grind)
    | (have i₁ := eq801 X0
       have i₂ := eq300 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq300 eq801
    | (have j1 := eq300 X1 X0
       grind)
    | exact resolve eq801 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq18004 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17910 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17910
  have eq18027 : x = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17902
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17902
    | exact resolve eq17902 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17902
  have eq18055 : x = y ∨ x = (k x y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18027
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq18027
    | exact resolve eq18027 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18027
  have eq18056 : x = (k x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq18055
  have eq18104 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18056
       grind)
    | exact superpose eq18056 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18056
  have eq18116 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq18104
  have eq19032 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18116
       grind)
    | exact superpose eq18116 eq28
    | exact resolve eq28 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19034 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq29 x x y
       have i₂ := eq18116
       grind)
    | exact superpose eq18116 eq29
    | exact resolve eq29 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq19800 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq19032
       grind)
    | exact superpose eq19032 eq28
    | exact resolve eq28 eq19032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19032
  have eq20650 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0
       have i₂ := eq740 (σ X0) X1
       grind)
    | exact superpose eq740 eq801
    | (have j1 := eq740 (σ X1) X0
       grind)
    | exact resolve eq801 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq20806 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20650 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20650
    | (have j0 := eq20650 X0 X1
       grind)
    | exact resolve eq20650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20650
  have eq20880 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20806 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20806
    | (have j0 := eq20806 X0 X1
       grind)
    | exact resolve eq20806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20806
  have eq20911 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20880 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq20880
    | (have j0 := eq20880 X0 X1
       grind)
    | exact resolve eq20880 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20880
  have eq20923 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20911 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq20911
    | (have j0 := eq20911 X0 X1
       grind)
    | exact resolve eq20911 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20911
  have eq20924 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20923 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20923
  have eq67497 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) (σ X1)
       have i₂ := eq18004 X1 X0
       grind)
    | exact superpose eq18004 eq22
    | (have j1 := eq18004 (σ X0) (M.op (σ (k X0 X1)) (σ X0))
       grind)
    | exact resolve eq22 eq18004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18004
  have eq71114 : (k y x) = (τ (σ x)) ∨ x = y ∨ y = (k y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20924 x y
       have i₂ := eq5754
       grind)
    | exact superpose eq5754 eq20924
    | (have j0 := eq20924 x y
       grind)
    | exact resolve eq20924 eq5754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5754 eq20924
  have eq71214 : (k y x) = (τ (σ x)) ∨ x = y ∨ y = (k y x) ∨ x = (M.op y x) := by grind
  clear eq71114
  have eq71246 : y = (k y x) ∨ x = y ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq71214
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq71214
    | exact resolve eq71214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71214
  have eq120816 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq71246
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq71246
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq71246 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71246
  have eq120893 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq120816
  have eq121593 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19034 y
       have i₂ := eq120893
       grind)
    | exact superpose eq120893 eq19034
    | exact resolve eq19034 eq120893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19034 eq120893
  have eq121775 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq121593
  have eq125297 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq22 y x
       have i₂ := eq121775
       grind)
    | exact superpose eq121775 eq22
    | exact resolve eq22 eq121775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121775
  have eq126857 : x = y ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq18116
       have i₂ := eq125297
       grind)
    | exact superpose eq125297 eq18116
    | exact resolve eq18116 eq125297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18116 eq125297
  have eq126998 : y = (M.op x x) ∨ x = y := by grind
  clear eq126857
  have eq128102 : x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq22 x x
       have i₂ := eq126998
       grind)
    | exact superpose eq126998 eq22
    | exact resolve eq22 eq126998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128132 : ∀ X0 X1 : G, x = (M.op (M.op X1 X0) x) ∨ (k y X0) = (M.op y X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1 x x
       have i₂ := eq126998
       grind)
    | exact superpose eq126998 eq135
    | (have j0 := eq135 X0 X1 x x
       grind)
    | exact resolve eq135 eq126998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq228795 : x = (M.op x x) ∨ x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq128132 x y
       have i₂ := eq128102
       grind)
    | exact superpose eq128102 eq128132
    | exact resolve eq128132 eq128102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128102 eq128132
  have eq228971 : x = (k y x) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq228795
  have eq229491 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq67497 y x
       have i₂ := eq228971
       grind)
    | exact superpose eq228971 eq67497
    | (have j0 := eq67497 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq67497 eq228971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67497 eq228971
  have eq229492 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq229491
  have eq230573 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq229492
       grind)
    | exact superpose eq229492 eq14
    | exact resolve eq14 eq229492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229492
  have eq232778 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq230573
       have i₂ := eq19800
       grind)
    | exact superpose eq19800 eq230573
    | exact resolve eq230573 eq19800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19800 eq230573
  have eq232795 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq232778
  have eq232796 : x = (M.op x x) ∨ x = y := by grind
  clear eq232795
  have eq234931 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq126998
       have i₂ := eq232796
       grind)
    | exact superpose eq232796 eq126998
    | exact resolve eq126998 eq232796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126998 eq232796
  have eq235171 : x = y := by grind
  clear eq234931
  have eq235832 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq235171
       grind)
    | exact superpose eq235171 eq14
    | exact resolve eq14 eq235171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235171
  have eq239024 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq235832
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq235832
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq235832
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq235832
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq235832 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239025 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq235832
       have i₂ := eq403 (σ x) X0
       grind)
    | exact superpose eq403 eq235832
    | (have j1 := eq403 (σ x) X0
       grind)
    | exact resolve eq235832 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq256471 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq239024 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239024
  have eq257048 : (τ (M.op (σ x) (σ (M.op x x)))) = (k (τ (σ x)) (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq117 (σ x) (M.op x x)
       have i₂ := eq256471
       grind)
    | exact superpose eq256471 eq117
    | (have j0 := eq117 (M.op (σ x) (σ (M.op x x))) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq117 eq256471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256471
  have eq257049 : (k x (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq257048
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq257048
    | exact resolve eq257048 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257048
  have eq257054 : (M.op (M.op x x) x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq257049
  have eq257058 : x = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq257054
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq257054
    | exact resolve eq257054 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257054
  have eq257060 : x = (τ (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq257058
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq257058
    | exact resolve eq257058 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257058
  have eq910182 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1441 X0 (τ X0)
       have i₂ := eq22 (τ X0) (τ X0)
       grind)
    | exact superpose eq22 eq1441
    | (have j0 := eq1441 X0 (τ X0)
       grind)
    | exact resolve eq1441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq910188 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq910182 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq910182
    | (have j0 := eq910182 X0
       grind)
    | exact resolve eq910182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910182
  have eq916379 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq910188 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq910188
    | exact resolve eq910188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910188
  have eq916445 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq916379 X0
       grind)
    | exact superpose eq916379 eq66
    | (have j0 := eq66 (σ X0) (σ (M.op X0 X0))
       have j1 := eq916379 X0
       grind)
    | exact resolve eq66 eq916379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916379
  have eq916450 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq916445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916445
  have eq921735 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq916450 X0
       grind)
    | exact superpose eq916450 eq22
    | (have j1 := eq916450 X0
       grind)
    | exact resolve eq22 eq916450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916450
  have eq928508 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq257060
       have i₂ := eq921735 x
       grind)
    | exact superpose eq921735 eq257060
    | (have j1 := eq921735 x
       grind)
    | exact resolve eq257060 eq921735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257060 eq921735
  have eq928571 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) := by grind
  clear eq928508
  have eq928582 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq928571
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq928571
    | exact resolve eq928571 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928571
  have eq928583 : x = (M.op x x) := by grind
  clear eq928582
  have eq930220 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq239025 X0
       have i₂ := eq928583
       grind)
    | exact superpose eq928583 eq239025
    | (have j0 := eq239025 X0
       grind)
    | exact resolve eq239025 eq928583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239025
  have eq930325 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq107 x x
       have i₂ := eq928583
       grind)
    | exact superpose eq928583 eq107
    | exact resolve eq107 eq928583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq930579 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq930220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930220
  have eq938626 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ X0) x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq117 X0 x
       have i₂ := eq930579 X0
       grind)
    | exact superpose eq930579 eq117
    | (have j0 := eq117 (M.op X0 (σ x)) (k (τ X0) x)
       grind)
    | exact resolve eq117 eq930579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq930579
  have eq940203 : x = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq801 x
       have i₂ := eq930325 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq930325 eq801
    | (have j0 := eq801 x
       have j1 := eq930325 (M.op x (τ (M.op (σ x) (σ x))))
       grind)
    | exact resolve eq801 eq930325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq930325
  have eq940204 : x = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq940203
  have eq990625 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq938626 (M.op (σ x) X0)
       have i₂ := eq22 (σ x) X0
       grind)
    | exact superpose eq22 eq938626
    | (have j0 := eq938626 (M.op (σ x) X0)
       grind)
    | exact resolve eq938626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938626
  have eq990670 : ∀ X0 : G, x = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq990625 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq990625
    | (have j0 := eq990625 X0
       grind)
    | exact resolve eq990625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990625
  have eq1040095 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq66 x (τ (M.op (σ x) X0))
       have i₂ := eq990670 X0
       grind)
    | exact superpose eq990670 eq66
    | (have j0 := eq66 x (τ (M.op (σ x) X0))
       have j1 := eq990670 X0
       grind)
    | exact resolve eq66 eq990670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq990670
  have eq1040102 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq1040095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040095
  have eq1044649 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op x (τ (M.op (σ x) X0))) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (τ (M.op (σ x) X0)) x
       have i₂ := eq1040102 X0
       grind)
    | exact superpose eq1040102 eq22
    | (have j1 := eq1040102 X0
       grind)
    | exact resolve eq22 eq1040102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1040102
  have eq1943631 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq940204
       have i₂ := eq1044649 (σ x)
       grind)
    | exact superpose eq1044649 eq940204
    | (have j1 := eq1044649 (σ x)
       grind)
    | exact resolve eq940204 eq1044649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940204 eq1044649
  have eq1943661 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq1943631
  have eq1943752 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq1943661
       grind)
    | exact superpose eq1943661 eq10
    | exact resolve eq10 eq1943661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943661
  have eq1954847 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq235832
       have i₂ := eq1943752
       grind)
    | exact superpose eq1943752 eq235832
    | exact resolve eq235832 eq1943752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235832 eq1943752
  have eq1955241 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1954847
       have i₂ := eq928583
       grind)
    | exact superpose eq928583 eq1954847
    | exact resolve eq1954847 eq928583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928583 eq1954847
  have eq1955242 : False := by grind
  exact eq1955242

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation2322 : Law3.StructuralFromFin Law2322 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V4_Equation2322

/-- `Equation2333`: `x = (y ◇ (y ◇ (x ◇ z))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if X = m(Y,Y) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G1V0_Equation2333 :
    AutBox.GuardFix (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2333 := by
  classical
  refine AutBox.guardFix_of (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law2333.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 (M.op X0 X2))) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X2 (M.op (M.op X0 X1) X3))) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 (M.op X2 (M.op X2 (M.op (M.op X0 X1) X3))) X1
       have i₂ := eq8 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1 x x
       have i₂ := eq8 (M.op X0 X1) x x
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = X1 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X1 X2) X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X1 (M.op X0 X2)) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 (M.op X1 X2)
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X1 (M.op X1 (M.op X0 X2))) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
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
  have eq25 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X0 X2
       have i₂ := eq24 X0 (M.op X0 X2)
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
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
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq24 X0 (M.op X1 X2)
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq20 (σ X0) (σ X1)
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 (σ X0) (k (σ X0) (σ X1))
       have j1 := eq20 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq20 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq48 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X1 (M.op X0 X2) X0
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq39
    | exact resolve eq39 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq30
    | (have j0 := eq30 X0 (M.op X1 X1)
       have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
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
  have eq76 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq83 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
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
  clear eq31
  have eq98 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X1 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq48 X0 X1 X2
       have i₂ := eq12 (M.op X0 X2) X1
       grind)
    | exact superpose eq12 eq48
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq106 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X2 X0) (M.op X0 X1)
       have i₂ := eq48 X0 X2 X1
       grind)
    | exact superpose eq48 eq18
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq201 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq104 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq104
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq104 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X0) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq22 X2 X0 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 (M.op (M.op X0 X1) X2) X0
       have j1 := eq22 X2 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq408 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33
    | (have j0 := eq33 (σ (k X1 (τ X0))) (M.op (σ X1) X0)
       grind)
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 := by
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
  have eq422 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) (σ X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq45
    | (have j0 := eq45 (σ X0) (σ X1)
       have j1 := eq33 X0 X1
       grind)
    | (have r₁ := eq45 (σ X0) (σ X0)
       have r₂ := eq33 X0 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq33 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq33 X0 (M.op X0 X1)
       grind)
    | exact resolve eq45 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq45
  have eq646 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq201 X0 X1
       grind)
    | exact superpose eq201 eq36
    | (have j0 := eq36 X0 X1
       have j1 := eq201 X0 X1
       grind)
    | exact resolve eq36 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq652 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq646 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq658 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67
    | (have j0 := eq67 (k X1 X0) (k (τ X1) (τ X0))
       grind)
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1269 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X0) X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | (have j1 := eq64 X0 X1
       grind)
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1330 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (M.op X1 X1))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 X1 X1
       have i₂ := eq64 X0 (M.op X1 X1)
       grind)
    | exact superpose eq64 eq106
    | (have j1 := eq64 X0 (M.op X1 X1)
       grind)
    | exact resolve eq106 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1337 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1342 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (M.op X1 X1))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1506 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X2 ∨ (k X2 X1) = (M.op X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X2 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq98 X0 X1 X2
       have i₂ := eq12 (M.op X2 X1) X1
       grind)
    | exact superpose eq12 eq98
    | (have j0 := eq98 X2 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | exact resolve eq98 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1845 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq408 X0 X1
       grind)
    | exact superpose eq408 eq9
    | (have j1 := eq408 X0 X1
       grind)
    | exact resolve eq9 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq2065 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq67
    | (have j0 := eq67 (σ X0) (k (τ (σ X0)) X1)
       have j1 := eq44 X0 X1
       grind)
    | exact resolve eq67 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq2076 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2065 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2065
    | (have j0 := eq2065 X0 X1
       grind)
    | exact resolve eq2065 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2078 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2076 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2076
    | (have j0 := eq2076 X0 X1
       grind)
    | exact resolve eq2076 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076
  have eq2079 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2078 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq2924 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X1 X0)) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq417 X1 X0
       grind)
    | exact superpose eq417 eq9
    | (have j1 := eq417 X1 X0
       grind)
    | exact resolve eq9 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17358 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1254 X0 X1
       grind)
    | exact superpose eq1254 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1254 X0 X1
       grind)
    | exact resolve eq13 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq17621 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17358
  have eq18456 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq18472 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X1
       have i₂ := eq17621 X0 X1
       grind)
    | (have i₁ := eq24 X0 X1
       have i₂ := eq17621 (M.op X0 X1) X1
       grind)
    | exact superpose eq17621 eq24
    | (have j1 := eq17621 X0 X1
       grind)
    | exact resolve eq24 eq17621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17621
  have eq21874 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq2079 x y
       grind)
    | exact superpose eq2079 eq14
    | (have j1 := eq2079 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq2079 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2079 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21891 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq2079 X0 X1
       grind)
    | exact superpose eq2079 eq18
    | (have j1 := eq2079 X0 X1
       grind)
    | exact resolve eq18 eq2079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq21975 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21874
       have i₂ := eq25 x y
       grind)
    | exact superpose eq25 eq21874
    | (have j1 := eq25 x y
       grind)
    | exact resolve eq21874 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq21976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq21874
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq21874
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq21874 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq21978 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21874
       have i₂ := eq652 x y
       grind)
    | exact superpose eq652 eq21874
    | (have j1 := eq652 x x
       grind)
    | exact resolve eq21874 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq21874
       have i₂ := eq18456 x y
       grind)
    | exact superpose eq18456 eq21874
    | (have j1 := eq18456 x y
       grind)
    | (have r₁ := eq21874
       have r₂ := eq18456 x y
       grind)
    | (have r₁ := eq21874
       have r₂ := eq18456 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq21874
       have r₂ := eq18456 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq21874 eq18456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18456 eq21874
  have eq21989 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ x = y := by grind
  clear eq21981
  have eq21990 : x = (k x y) ∨ x = y := by grind
  clear eq21989
  have eq21994 : x = (M.op x y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq21978
  have eq21996 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq21976
  have eq21997 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq21975
  have eq22445 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq417 x y
       have i₂ := eq21990
       grind)
    | exact superpose eq21990 eq417
    | (have j0 := eq417 x y
       grind)
    | exact resolve eq417 eq21990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq22459 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq18472 x y
       have i₂ := eq21990
       grind)
    | exact superpose eq21990 eq18472
    | (have j0 := eq18472 x y
       grind)
    | exact resolve eq18472 eq21990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18472
  have eq22460 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq22459
  have eq22467 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq22445
  have eq24478 : x = (M.op x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24 x y
       have i₂ := eq21994
       grind)
    | exact superpose eq21994 eq24
    | exact resolve eq24 eq21994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21994
  have eq24554 : x = (M.op x x) ∨ x = y := by grind
  clear eq24478
  have eq24822 : ∀ X0 : G, x ≠ x ∨ (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1337 X0 x
       have i₂ := eq24554
       grind)
    | exact superpose eq24554 eq1337
    | (have j0 := eq1337 X0 x
       grind)
    | (have r₁ := eq1337 X0 x
       have r₂ := eq24554
       grind)
    | exact resolve eq1337 eq24554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq24909 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x ∨ x = y := by
    intro X0
    first
    | (have j0 := eq24822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24822
  have eq24991 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (k (σ X0) (σ X1))) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1269 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1269
    | (have j0 := eq1269 (k (σ X0) (σ X1)) (M.op X0 X1)
       grind)
    | exact resolve eq1269 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25312 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) X1) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X0) (τ X1)) = (τ (k X0 (σ (τ X1)))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0
       have i₂ := eq1269 X0 (τ X0)
       grind)
    | exact superpose eq1269 eq76
    | (have j1 := eq1269 X0 (τ X1)
       grind)
    | exact resolve eq76 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1269
  have eq25317 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) X1) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X0) (τ X1)) = (τ (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq25312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25312
  have eq25384 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ X0) = (τ X1) ∨ (M.op (τ X0) (τ X1)) = (τ (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25317 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25317
    | (have j0 := eq25317 X0 X1
       grind)
    | exact resolve eq25317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25317
  have eq25412 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25384 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq25384
    | (have j0 := eq25384 X0 X1
       grind)
    | exact resolve eq25384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25384
  have eq27176 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (τ X1)
       have i₂ := eq1845 X1 (τ X0)
       grind)
    | exact superpose eq1845 eq30
    | (have j0 := eq30 X0 (τ X1)
       have j1 := eq1845 X1 (τ X0)
       grind)
    | exact resolve eq30 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1845
  have eq27321 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27176 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27176
  have eq27391 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (σ (τ X1))) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27321 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27321
    | (have j0 := eq27321 X0 X1
       grind)
    | exact resolve eq27321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27321
  have eq27438 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27391 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq27391
    | (have j0 := eq27391 X0 X1
       grind)
    | exact resolve eq27391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27391
  have eq37970 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (τ X0) = (τ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (τ X0) = (τ X1) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2924 (τ X1) (τ X0)
       have i₂ := eq658 X1 X0
       grind)
    | exact superpose eq658 eq2924
    | (have j0 := eq2924 (τ X1) (τ X0)
       have j1 := eq658 X0 (M.op (σ (τ X1)) (σ (τ X1)))
       grind)
    | exact resolve eq2924 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq2924
  have eq38383 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (τ X0) = (τ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have j0 := eq37970 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37970
  have eq38438 : ∀ X0 X1 : G, (M.op (σ (τ (k X0 X1))) X0) = X0 ∨ (τ X0) = (τ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38383 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38383
    | (have j0 := eq38383 X0 X1
       grind)
    | exact resolve eq38383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38383
  have eq38453 : ∀ X0 X1 : G, (M.op (k X0 X1) X0) = X0 ∨ (τ X0) = (τ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38438 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq38438
    | (have j0 := eq38438 X0 X1
       grind)
    | exact resolve eq38438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38438
  have eq38459 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (M.op (k X0 X1) X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38453 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38453
    | (have j0 := eq38453 X0 X1
       grind)
    | exact resolve eq38453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38453
  have eq47525 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ x = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24909 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24909
    | exact resolve eq24909 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24909
  have eq57952 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (τ (k (σ X0) (σ X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24991 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24991
  have eq64069 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq422 x y
       have i₂ := eq21990
       grind)
    | exact superpose eq21990 eq422
    | (have j0 := eq422 x y
       grind)
    | exact resolve eq422 eq21990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq21990
  have eq64158 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq64069
  have eq64159 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq64158
  have eq66231 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (τ (k (σ X0) (σ x))) ∨ x = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq57952 X0 x
       have i₂ := eq24554
       grind)
    | exact superpose eq24554 eq57952
    | (have j0 := eq57952 X0 x
       grind)
    | (have r₁ := eq57952 X0 x
       have r₂ := eq24554
       grind)
    | exact resolve eq57952 eq24554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24554 eq57952
  have eq66233 : ∀ X0 : G, (M.op X0 x) = (τ (k (σ X0) (σ x))) ∨ x = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq66231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66231
  have eq115258 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27438 X1 (M.op X0 X0)
       have i₂ := eq106 X0 X0 X0
       grind)
    | exact superpose eq106 eq27438
    | (have j0 := eq27438 X1 (M.op X0 X0)
       grind)
    | exact resolve eq27438 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27438
  have eq115297 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq115258 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115258
  have eq115761 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (M.op (k X1 (M.op X0 X0)) X1) = X1 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38459 X1 (M.op X0 X0)
       have i₂ := eq106 X0 X0 X0
       grind)
    | exact superpose eq106 eq38459
    | (have j0 := eq38459 X1 (M.op X0 X0)
       grind)
    | exact resolve eq38459 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq38459
  have eq115932 : ∀ X0 X1 : G, (M.op (k X1 (M.op X0 X0)) X1) = X1 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq115761 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115761
  have eq153762 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236 X0 (M.op X1 X2) X1
       have i₂ := eq39 X0 X1 X2
       grind)
    | exact superpose eq39 eq236
    | (have j0 := eq236 X1 (M.op X0 X2) X0
       grind)
    | (have r₁ := eq236 X1 (M.op X1 X2) X1
       have r₂ := eq39 X1 X1 X2
       grind)
    | exact resolve eq236 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq236
  have eq153859 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 (M.op X0 X2)) = (k X0 (M.op X1 (M.op X0 X2))) ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153762 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq153762
    | (have j0 := eq153762 X0 X1 X2
       grind)
    | (have r₁ := eq153762 (M.op X1 (M.op X0 X2)) (M.op X0 (M.op X1 (M.op X0 X2))) X2
       have r₂ := eq29 X0 X1 X2
       grind)
    | (have r₁ := eq153762 (M.op X0 (M.op X1 (M.op X0 X2))) (M.op X1 (M.op X0 X2)) X2
       have r₂ := eq29 X0 X1 X2
       grind)
    | exact resolve eq153762 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq153762
  have eq162945 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq104 (σ y)
       have i₂ := eq22467
       grind)
    | exact superpose eq22467 eq104
    | exact resolve eq104 eq22467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq22467
  have eq184548 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq64159
       grind)
    | exact superpose eq64159 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq64159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64159
  have eq184553 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq184548
  have eq199162 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq652 (σ x) (σ x)
       have i₂ := eq162945
       grind)
    | exact superpose eq162945 eq652
    | (have j0 := eq652 (σ x) x
       grind)
    | exact resolve eq652 eq162945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162945
  have eq199163 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq199162
  have eq201531 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (τ X0) = (τ (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq115297 (σ x) x
       have i₂ := eq199163
       grind)
    | exact superpose eq199163 eq115297
    | exact resolve eq115297 eq199163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115297
  have eq201533 : ∀ X0 : G, (M.op (k X0 (σ x)) X0) = X0 ∨ (τ X0) = (τ (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq115932 (σ x) x
       have i₂ := eq199163
       grind)
    | exact superpose eq199163 eq115932
    | exact resolve eq115932 eq199163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115932 eq199163
  have eq201696 : ∀ X0 : G, (M.op (k X0 (σ x)) X0) = X0 ∨ (τ X0) = x ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq201533 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq201533
    | (have j0 := eq201533 X0
       grind)
    | exact resolve eq201533 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201533
  have eq201698 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (τ X0) = x ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq201531 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq201531
    | (have j0 := eq201531 X0
       grind)
    | exact resolve eq201531 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201531
  have eq210638 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 x)) (σ X0)) ∨ (τ (σ X0)) = x ∨ x = y ∨ x = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq201696 (σ X0)
       have i₂ := eq47525 X0
       grind)
    | exact superpose eq47525 eq201696
    | (have j0 := eq201696 (σ X0)
       have j1 := eq47525 (τ (σ X0))
       grind)
    | exact resolve eq201696 eq47525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47525 eq201696
  have eq210978 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 x)) (σ X0)) ∨ (τ (σ X0)) = x ∨ x = y ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq210638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210638
  have eq210992 : ∀ X0 : G, x = X0 ∨ (σ X0) = (M.op (σ (M.op X0 x)) (σ X0)) ∨ x = y ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq210978 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq210978
    | (have j0 := eq210978 X0
       grind)
    | exact resolve eq210978 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210978
  have eq210993 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 x)) (σ X0)) ∨ x = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq210992 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210992
  have eq212932 : ∀ X0 : G, (M.op X0 x) = (τ (M.op (σ X0) (σ x))) ∨ x = X0 ∨ x = y ∨ (τ (σ X0)) = x ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq66233 X0
       have i₂ := eq201698 (σ X0)
       grind)
    | exact superpose eq201698 eq66233
    | (have j0 := eq66233 X0
       have j1 := eq201698 (σ X0)
       grind)
    | exact resolve eq66233 eq201698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66233 eq201698
  have eq212962 : ∀ X0 : G, (M.op X0 x) = (τ (M.op (σ X0) (σ x))) ∨ x = X0 ∨ x = y ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have j0 := eq212932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212932
  have eq213004 : ∀ X0 : G, x = X0 ∨ (M.op X0 x) = (τ (M.op (σ X0) (σ x))) ∨ x = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq212962 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq212962
    | (have j0 := eq212962 X0
       grind)
    | exact resolve eq212962 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212962
  have eq213005 : ∀ X0 : G, (M.op X0 x) = (τ (M.op (σ X0) (σ x))) ∨ x = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq213004 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213004
  have eq219448 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq210993 y
       have i₂ := eq21996
       grind)
    | exact superpose eq21996 eq210993
    | (have j0 := eq210993 y
       grind)
    | exact resolve eq210993 eq21996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21996 eq210993
  have eq219567 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq219448
  have eq225728 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq219567
       grind)
    | exact superpose eq219567 eq14
    | exact resolve eq14 eq219567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219567
  have eq227935 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq225728
       have i₂ := eq21997
       grind)
    | exact superpose eq21997 eq225728
    | exact resolve eq225728 eq21997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21997 eq225728
  have eq227948 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq227935
  have eq227949 : x = (M.op x y) ∨ x = y := by grind
  clear eq227948
  have eq399631 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24 (σ y) (σ y)
       have i₂ := eq184553
       grind)
    | exact superpose eq184553 eq24
    | exact resolve eq24 eq184553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184553
  have eq425973 : (M.op y x) = (τ (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq213005 y
       have i₂ := eq399631
       grind)
    | exact superpose eq399631 eq213005
    | (have j0 := eq213005 y
       grind)
    | exact resolve eq213005 eq399631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213005 eq399631
  have eq426026 : (M.op y x) = (τ (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq425973
  have eq426035 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq426026
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq426026
    | exact resolve eq426026 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426026
  have eq427345 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq426035
       grind)
    | exact superpose eq426035 eq14
    | exact resolve eq14 eq426035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426035
  have eq428754 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq427345
       have i₂ := eq22460
       grind)
    | exact superpose eq22460 eq427345
    | (have r₁ := eq427345
       have r₂ := eq22460
       grind)
    | exact resolve eq427345 eq22460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22460 eq427345
  have eq428755 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq428754
  have eq428756 : x = (M.op y x) ∨ x = y := by grind
  clear eq428755
  have eq429957 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18 y x
       have i₂ := eq428756
       grind)
    | exact superpose eq428756 eq18
    | exact resolve eq18 eq428756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428756
  have eq431293 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq227949
       have i₂ := eq429957
       grind)
    | exact superpose eq429957 eq227949
    | exact resolve eq227949 eq429957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227949 eq429957
  have eq431470 : x = y := by grind
  clear eq431293
  have eq434114 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq431470
       grind)
    | exact superpose eq431470 eq14
    | exact resolve eq14 eq431470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431470
  have eq447381 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq434114
       have i₂ := eq12 X0 (σ x)
       grind)
    | (have i₁ := eq434114
       have i₂ := eq12 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq12 eq434114
    | (have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq434114
       have r₂ := eq12 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq434114 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447384 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq434114
       have i₂ := eq1506 (σ x) X0 (σ x)
       grind)
    | exact superpose eq1506 eq434114
    | (have j1 := eq1506 (σ x) X0 (σ x)
       grind)
    | exact resolve eq434114 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq447387 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq447384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447384
  have eq483279 : (k (σ (M.op x x)) (σ x)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have j0 := eq447381 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447381
  have eq483296 : (τ (M.op (σ (M.op x x)) (σ x))) = (k (τ (σ (M.op x x))) x) ∨ x = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq67 (σ (M.op x x)) x
       have i₂ := eq483279
       grind)
    | exact superpose eq483279 eq67
    | (have j0 := eq67 (M.op (σ (M.op x x)) (σ x)) (k (τ (σ (M.op x x))) x)
       grind)
    | exact resolve eq67 eq483279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq483279
  have eq483297 : (k (M.op x x) x) = (τ (M.op (σ (M.op x x)) (σ x))) ∨ x = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq483296
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq483296
    | exact resolve eq483296 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483296
  have eq483301 : (M.op x x) = (τ (M.op (σ (M.op x x)) (σ x))) ∨ x = (τ (σ (M.op x x))) := by grind
  clear eq483297
  have eq483303 : (M.op x x) = (τ (M.op (σ (M.op x x)) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq483301
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq483301
    | exact resolve eq483301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483301
  have eq648589 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (k X0 X1)) (τ X0)) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (τ X0) (τ X1)
       have i₂ := eq25412 X0 X1
       grind)
    | exact superpose eq25412 eq18
    | (have j1 := eq25412 X0 X1
       grind)
    | exact resolve eq18 eq25412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25412
  have eq679189 : ∀ X0 X1 : G, (M.op (τ (k (σ X0) X1)) X0) = X0 ∨ (σ X0) = (k (σ X0) X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq648589 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq648589
    | (have j0 := eq648589 (σ X0) X1
       grind)
    | exact resolve eq648589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648589
  have eq693070 : ∀ X0 X1 : G, (M.op (k X0 (τ X1)) X0) = X0 ∨ (σ X0) = (k (σ X0) X1) ∨ (τ X1) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq679189 X0 X1
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq679189
    | (have j0 := eq679189 X0 X1
       have j1 := eq83 X0 X1
       grind)
    | exact resolve eq679189 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679189
  have eq693210 : ∀ X0 X1 : G, (M.op (k X0 (τ X1)) X0) = X0 ∨ (σ X0) = (k (σ X0) X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq693070 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693070
  have eq693437 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (k X1 X0) X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq693210 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq693210
    | (have j0 := eq693210 X1 (σ X0)
       grind)
    | exact resolve eq693210 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693210
  have eq693654 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (k X0 X1) X0
       have i₂ := eq693437 X1 X0
       grind)
    | exact superpose eq693437 eq18
    | (have j1 := eq693437 X1 X0
       grind)
    | exact resolve eq18 eq693437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693437
  have eq913703 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq153859 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153859
  have eq913704 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq913703 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq913703
    | (have j0 := eq913703 X0 X1
       grind)
    | exact resolve eq913703 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913703
  have eq913705 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq913704 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq913704 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq913704
    | (have j0 := eq913704 X1 X1
       have j1 := eq12 X0 X1
       grind)
    | exact resolve eq913704 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913704
  have eq914111 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X0
       have i₂ := eq913705 X1 X0
       grind)
    | exact superpose eq913705 eq652
    | (have j0 := eq652 X0 X1
       have j1 := eq913705 X1 X0
       grind)
    | exact resolve eq652 eq913705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq913705
  have eq914146 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq914111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914111
  have eq914307 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq914146
  have eq914335 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq914307 X0
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq914307
    | (have j0 := eq914307 X0
       grind)
    | exact resolve eq914307 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914307
  have eq914336 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq914335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914335
  have eq914466 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21891 X0 (M.op X0 X0)
       have i₂ := eq914336 X0
       grind)
    | exact superpose eq914336 eq21891
    | (have j0 := eq21891 (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))
       have j1 := eq914336 X0
       grind)
    | exact resolve eq21891 eq914336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21891 eq914336
  have eq914508 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq914466 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914466
  have eq914854 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq483303
       have i₂ := eq914508 x
       grind)
    | exact superpose eq914508 eq483303
    | (have j1 := eq914508 x
       grind)
    | exact resolve eq483303 eq914508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483303 eq914508
  have eq915032 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq914854
  have eq915041 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq915032
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq915032
    | exact resolve eq915032 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915032
  have eq915042 : x = (M.op x x) := by grind
  clear eq915041
  have eq915054 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq447387 X0
       have i₂ := eq915042
       grind)
    | exact superpose eq915042 eq447387
    | (have j0 := eq447387 X0
       grind)
    | exact resolve eq447387 eq915042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447387
  have eq915152 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq1342 X0 x
       have i₂ := eq915042
       grind)
    | exact superpose eq915042 eq1342
    | exact resolve eq1342 eq915042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq915415 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq915054 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915054
  have eq917426 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k x (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq83 x X0
       have i₂ := eq915415 X0
       grind)
    | exact superpose eq915415 eq83
    | (have j0 := eq83 (k x (τ X0)) (M.op (σ x) X0)
       grind)
    | exact resolve eq83 eq915415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq917480 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ X0)) ∨ (k x X0) = (M.op x (k x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq693654 x X0
       have i₂ := eq915415 (σ X0)
       grind)
    | exact superpose eq915415 eq693654
    | (have j0 := eq693654 x X0
       grind)
    | exact resolve eq693654 eq915415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693654 eq915415
  have eq945944 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k x (τ (M.op (σ x) X0))) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq917426 (M.op (σ x) X0)
       have i₂ := eq24 (σ x) X0
       grind)
    | exact superpose eq24 eq917426
    | (have j0 := eq917426 (M.op (σ x) X0)
       grind)
    | exact resolve eq917426 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917426
  have eq1237355 : ∀ X0 : G, (k x X0) = (M.op x (k x X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq24 (σ x) (σ X0)
       have i₂ := eq917480 X0
       grind)
    | exact superpose eq917480 eq24
    | (have j1 := eq917480 X0
       grind)
    | exact resolve eq24 eq917480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq917480
  have eq1275099 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k x X0) = (M.op x (k x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq434114
       have i₂ := eq1237355 X0
       grind)
    | exact superpose eq1237355 eq434114
    | (have j1 := eq1237355 X0
       grind)
    | exact resolve eq434114 eq1237355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237355
  have eq1275122 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k x X0) = (M.op x (k x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq1275099 X0
       have i₂ := eq915042
       grind)
    | exact superpose eq915042 eq1275099
    | (have j0 := eq1275099 X0
       grind)
    | exact resolve eq1275099 eq915042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275099
  have eq1275123 : ∀ X0 : G, (k x X0) = (M.op x (k x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq1275122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275122
  have eq1275253 : ∀ X0 : G, x = (M.op (k x X0) x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq18 x (k x X0)
       have i₂ := eq1275123 X0
       grind)
    | exact superpose eq1275123 eq18
    | (have j1 := eq1275123 (M.op (k x X0) x)
       grind)
    | exact resolve eq18 eq1275123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1275123
  have eq1275428 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1275253 (τ (M.op (σ x) X0))
       have i₂ := eq945944 X0
       grind)
    | exact superpose eq945944 eq1275253
    | (have j0 := eq1275253 (M.op (τ (M.op (σ x) X0)) x)
       have j1 := eq945944 X0
       grind)
    | exact resolve eq1275253 eq945944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945944 eq1275253
  have eq1275961 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq1275428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275428
  have eq1284826 : ∀ X0 : G, (σ x) = (k (M.op (σ x) X0) (σ x)) ∨ x = (τ (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq915152 (M.op (σ x) X0)
       have i₂ := eq1275961 X0
       grind)
    | exact superpose eq1275961 eq915152
    | (have j0 := eq915152 (M.op (σ x) X0)
       have j1 := eq1275961 X0
       grind)
    | exact resolve eq915152 eq1275961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915152 eq1275961
  have eq1285109 : ∀ X0 : G, (σ x) = (k (M.op (σ x) X0) (σ x)) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq1284826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284826
  have eq1285911 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1285109
  have eq1286090 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq1285911
       grind)
    | exact superpose eq1285911 eq10
    | exact resolve eq10 eq1285911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285911
  have eq1286091 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1286090
  have eq1286105 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq434114
       have i₂ := eq1286091
       grind)
    | exact superpose eq1286091 eq434114
    | exact resolve eq434114 eq1286091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434114 eq1286091
  have eq1286565 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1286105
       have i₂ := eq915042
       grind)
    | exact superpose eq915042 eq1286105
    | exact resolve eq1286105 eq915042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915042 eq1286105
  have eq1286566 : False := by grind
  exact eq1286566

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation2333 : Law3.StructuralFromFin Law2333 :=
  AutBox.structuralFromFin_boxIte (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G1V0_Equation2333

/-- `Equation2376`: `x = (y ◇ (z ◇ (x ◇ w))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V0_Equation2376 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2376 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law2376.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op x (M.op x (M.op (M.op X0 (M.op X1 X2)) x))) X0 X2
       have i₂ := eq8 (M.op X0 (M.op X1 X2)) x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = X2 ∨ (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op X2 X3) X3
       have i₂ := eq12 (M.op X2 X3) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X2 (M.op X0 X3))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X2 X3) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op x (M.op (M.op X0 X1) x)) X0 X1
       have i₂ := eq18 x (M.op X0 X1) x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 (M.op X0 X4)) X1 X2 X0
       have i₂ := eq18 X3 X0 X4
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X1) X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq28
    | exact resolve eq28 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 (M.op X0 X2) X0
       have i₂ := eq28 X0 X2
       grind)
    | exact superpose eq28 eq18
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq20 (σ X1) (σ X0)
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 (σ X0) (k (σ X0) (σ X1))
       have j1 := eq20 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq39 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq75 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq20 (τ X1) X0
       grind)
    | exact superpose eq20 eq34
    | (have j0 := eq34 X1 X0
       have j1 := eq20 (τ X1) X0
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq34
    | (have j0 := eq34 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq102 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq41 X0 X0 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq138 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq219 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X1 X0) (M.op X2 X3)) ∨ (k (M.op X0 X4) X3) = (M.op (M.op X0 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X1 (M.op X2 X3) X0
       have i₂ := eq22 X3 X2 X0 X4
       grind)
    | exact superpose eq22 eq18
    | (have j1 := eq22 X0 X1 (M.op X2 X3) X3
       grind)
    | exact resolve eq18 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq374 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq36 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq36 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq434 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq53
    | (have j0 := eq53 X0 X1
       have j1 := eq138 X0 X1
       grind)
    | exact resolve eq53 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq442 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq434 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq538 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq67
    | (have j0 := eq67 (M.op X0 (σ X1)) (k (τ X0) X1)
       have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  clear eq81
  have eq629 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq612
    | (have j0 := eq612 X0
       grind)
    | exact resolve eq612 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq1585 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1716 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X1 (M.op X2 X2)) ∨ (k (σ (M.op X1 (M.op X2 X2))) X0) = (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0))) ∨ (τ X0) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X2 X1 X2 X1 X2
       have i₂ := eq76 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq76 eq30
    | (have j1 := eq76 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact resolve eq30 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq76
  have eq1745 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 (M.op X2 X2))) X0) = (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0))) ∨ (τ X0) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1716 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq2000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq374
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq374
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq374 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq374
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq374
    | (have j1 := eq20 y x
       grind)
    | exact resolve eq374 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2004 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq374
       have i₂ := eq40 y x
       grind)
    | exact superpose eq40 eq374
    | (have j1 := eq40 y x
       grind)
    | exact resolve eq374 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq374
  have eq2010 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq2004
  have eq2011 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq2003
  have eq2014 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq2000
  have eq2202 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq67
    | (have j0 := eq67 (σ X0) (k (τ (σ X0)) X1)
       have j1 := eq48 X0 X1
       grind)
    | exact resolve eq67 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq2213 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2202 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2202
    | (have j0 := eq2202 X0 X1
       grind)
    | exact resolve eq2202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2215 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2213 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2213
    | (have j0 := eq2213 X0 X1
       grind)
    | exact resolve eq2213 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2216 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2215 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215
  have eq3583 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq2011
  have eq3774 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 (σ x) (σ x)
       have i₂ := eq2014
       grind)
    | exact superpose eq2014 eq39
    | exact resolve eq39 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq4558 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X1 X2) X1) = (k (M.op X1 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103 (M.op X2 x)
       have i₂ := eq219 x X2 X2 x x
       grind)
    | exact superpose eq219 eq103
    | (have j1 := eq219 X1 X1 X2 X1 X2
       grind)
    | exact resolve eq103 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq219
  have eq4620 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X1) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4558 X0 X1 X2
       have i₂ := eq28 X1 X2
       grind)
    | exact superpose eq28 eq4558
    | (have j0 := eq4558 X0 X1 X2
       grind)
    | exact resolve eq4558 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558
  have eq5299 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq28 (σ x) (σ x)
       have i₂ := eq2010
       grind)
    | exact superpose eq2010 eq28
    | exact resolve eq28 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq5736 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq67 (σ x) y
       have i₂ := eq3583
       grind)
    | exact superpose eq3583 eq67
    | (have j0 := eq67 (σ x) (k (τ (σ x)) y)
       grind)
    | exact resolve eq67 eq3583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583
  have eq5745 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq5736
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq5736
    | exact resolve eq5736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5736
  have eq5746 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y := by grind
  clear eq5745
  have eq5748 : x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5746
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq5746
    | exact resolve eq5746 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5746
  have eq5749 : x = (k x y) ∨ x = y := by grind
  clear eq5748
  have eq5907 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5749
       grind)
    | exact superpose eq5749 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5749
  have eq6048 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41 x x y
       have i₂ := eq5907
       grind)
    | exact superpose eq5907 eq41
    | exact resolve eq41 eq5907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5907
  have eq16097 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3774
       grind)
    | exact superpose eq3774 eq14
    | exact resolve eq14 eq3774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq39647 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1585 X1 X0
       grind)
    | exact superpose eq1585 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1585 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq13 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq39711 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39647 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39647
  have eq40903 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) (σ X1)
       have i₂ := eq2216 X0 X1
       grind)
    | exact superpose eq2216 eq28
    | (have j1 := eq2216 X0 X1
       grind)
    | exact resolve eq28 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq49741 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0
       have i₂ := eq538 (σ X0) X1
       grind)
    | exact superpose eq538 eq629
    | (have j1 := eq538 (σ X1) X0
       grind)
    | exact resolve eq629 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq629
  have eq49957 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49741 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49741
    | (have j0 := eq49741 X0 X1
       grind)
    | exact resolve eq49741 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49741
  have eq50075 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49957 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49957
    | (have j0 := eq49957 X0 X1
       grind)
    | exact resolve eq49957 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49957
  have eq50128 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50075 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq50075
    | (have j0 := eq50075 X0 X1
       grind)
    | exact resolve eq50075 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50075
  have eq50139 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50128 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq50128
    | (have j0 := eq50128 X0 X1
       grind)
    | exact resolve eq50128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50128
  have eq50140 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50139
  have eq93412 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40903 X0 X1
       have i₂ := eq39711 X0 X1
       grind)
    | exact superpose eq39711 eq40903
    | (have j0 := eq40903 X0 X1
       have j1 := eq39711 X0 X1
       grind)
    | exact resolve eq40903 eq39711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39711
  have eq93536 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq93412 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93412
  have eq93687 : (τ (σ x)) = (k y x) ∨ x = y ∨ y = (k y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq50140 x y
       have i₂ := eq5299
       grind)
    | exact superpose eq5299 eq50140
    | (have j0 := eq50140 x y
       grind)
    | exact resolve eq50140 eq5299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5299 eq50140
  have eq93705 : (τ (σ x)) = (k y x) ∨ x = y ∨ y = (k y x) ∨ x = (M.op y x) := by grind
  clear eq93687
  have eq93720 : y = (k y x) ∨ x = y ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq93705
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq93705
    | exact resolve eq93705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93705
  have eq96146 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k (M.op X1 X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq442 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq4620 X0 X1 X2
       grind)
    | exact superpose eq4620 eq442
    | (have j0 := eq442 (M.op X0 X1) X1
       have j1 := eq4620 X0 X1 X2
       grind)
    | exact resolve eq442 eq4620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4620
  have eq96147 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k (M.op X1 X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq96146 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96146
  have eq100087 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq93720
       have i₂ := eq53 x y
       grind)
    | exact superpose eq53 eq93720
    | (have j1 := eq53 x y
       grind)
    | exact resolve eq93720 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93720
  have eq100128 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq100087
  have eq100151 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6048 y
       have i₂ := eq100128
       grind)
    | exact superpose eq100128 eq6048
    | exact resolve eq6048 eq100128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048 eq100128
  have eq100310 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq100151
  have eq100676 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (M.op X1 X1))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1745 X0 (τ X0) X1
       have i₂ := eq28 (τ X0) (M.op X1 X1)
       grind)
    | exact superpose eq28 eq1745
    | (have j0 := eq1745 X0 (τ X0) X1
       grind)
    | exact resolve eq1745 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq100680 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (M.op X1 X1))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100676 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100676
    | (have j0 := eq100676 X0 X1
       grind)
    | exact resolve eq100676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100676
  have eq100879 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq100310
       grind)
    | exact superpose eq100310 eq28
    | exact resolve eq28 eq100310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100310
  have eq101043 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16097
       have i₂ := eq100879
       grind)
    | exact superpose eq100879 eq16097
    | exact resolve eq16097 eq100879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16097 eq100879
  have eq101224 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq101043
  have eq101225 : y = (M.op x x) ∨ x = y := by grind
  clear eq101224
  have eq101247 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq102 x x
       have i₂ := eq101225
       grind)
    | exact superpose eq101225 eq102
    | exact resolve eq102 eq101225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq101271 : x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq101225
       grind)
    | exact superpose eq101225 eq28
    | exact resolve eq28 eq101225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101277 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq39 x x
       have i₂ := eq101225
       grind)
    | exact superpose eq101225 eq39
    | exact resolve eq39 eq101225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101225
  have eq101736 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq93536 y x
       have i₂ := eq101271
       grind)
    | exact superpose eq101271 eq93536
    | (have j0 := eq93536 y x
       grind)
    | exact resolve eq93536 eq101271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93536
  have eq101737 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = y := by grind
  clear eq101736
  have eq120658 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq101737
       grind)
    | exact superpose eq101737 eq14
    | exact resolve eq14 eq101737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101737
  have eq120817 : (σ y) ≠ (σ y) ∨ y = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq120658
       have i₂ := eq101277
       grind)
    | exact superpose eq101277 eq120658
    | exact resolve eq120658 eq101277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101277 eq120658
  have eq120841 : (σ y) ≠ (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq120817
  have eq120842 : y = (k y x) ∨ x = y := by grind
  clear eq120841
  have eq120901 : y = (M.op y x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq101247 x
       have i₂ := eq120842
       grind)
    | exact superpose eq120842 eq101247
    | (have j0 := eq101247 (M.op y x)
       grind)
    | exact resolve eq101247 eq120842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101247 eq120842
  have eq120971 : y = (M.op y x) ∨ x = y := by grind
  clear eq120901
  have eq121033 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq101271
       have i₂ := eq120971
       grind)
    | exact superpose eq120971 eq101271
    | exact resolve eq101271 eq120971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101271 eq120971
  have eq121310 : x = y := by grind
  clear eq121033
  have eq121353 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq121310
       grind)
    | exact superpose eq121310 eq14
    | exact resolve eq14 eq121310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121310
  have eq121694 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq121353
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq121353
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq121353
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq121353
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq121353 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121695 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq121353
       have i₂ := eq442 (σ x) X0
       grind)
    | exact superpose eq442 eq121353
    | (have j1 := eq442 (σ x) X0
       grind)
    | exact resolve eq121353 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq123851 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq121694 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121694
  have eq123875 : (τ (M.op (σ x) (σ (M.op x x)))) = (k (τ (σ x)) (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq67 (σ x) (M.op x x)
       have i₂ := eq123851
       grind)
    | exact superpose eq123851 eq67
    | (have j0 := eq67 (M.op (σ x) (σ (M.op x x))) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq67 eq123851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123851
  have eq123876 : (k x (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq123875
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq123875
    | exact resolve eq123875 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123875
  have eq123883 : x = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq123876
  have eq123885 : x = (τ (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq123883
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq123883
    | exact resolve eq123883 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123883
  have eq140226 : ∀ X0 X3 : G, (k (M.op X0 X3) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq96147 (M.op X0 (M.op x x)) x x
       have i₂ := eq18 X0 x x
       grind)
    | exact superpose eq18 eq96147
    | (have j0 := eq96147 X0 X0 X3
       grind)
    | exact resolve eq96147 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq96147
  have eq140751 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140226 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq140226 X0 x
       have i₂ := eq12 X0 (M.op X0 x)
       grind)
    | exact superpose eq12 eq140226
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq140226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140226
  have eq141768 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40903 X0 X1
       have i₂ := eq140751 X0 X1
       grind)
    | exact superpose eq140751 eq40903
    | (have j0 := eq40903 (σ X1) (M.op (σ X0) (σ X1))
       have j1 := eq140751 X1 X0
       grind)
    | exact resolve eq40903 eq140751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40903 eq140751
  have eq141838 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq141768 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141768
  have eq147511 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (k x (M.op x x)) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq123885
       have i₂ := eq141838 x (M.op x x)
       grind)
    | exact superpose eq141838 eq123885
    | (have j1 := eq141838 x (M.op x x)
       grind)
    | exact resolve eq123885 eq141838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123885 eq141838
  have eq147633 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) ∨ (k x (M.op x x)) = (M.op x (M.op x x)) := by grind
  clear eq147511
  have eq147646 : x = (M.op x x) ∨ x = (M.op x x) ∨ (k x (M.op x x)) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq147633
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq147633
    | exact resolve eq147633 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147633
  have eq147647 : x = (M.op x x) ∨ (k x (M.op x x)) = (M.op x (M.op x x)) := by grind
  clear eq147646
  have eq147651 : (M.op x x) = (k x (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq147647
       have i₂ := eq39 x x
       grind)
    | exact superpose eq39 eq147647
    | exact resolve eq147647 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq147647
  have eq147654 : x = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq147651
  have eq147655 : x = (M.op x x) := by grind
  clear eq147654
  have eq147672 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq121695 X0
       have i₂ := eq147655
       grind)
    | exact superpose eq147655 eq121695
    | (have j0 := eq121695 X0
       grind)
    | exact resolve eq121695 eq147655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121695
  have eq148044 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq147672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147672
  have eq149730 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ X0) x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq67 X0 x
       have i₂ := eq148044 X0
       grind)
    | exact superpose eq148044 eq67
    | (have j0 := eq67 (M.op X0 (σ x)) (k (τ X0) x)
       grind)
    | exact resolve eq67 eq148044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq148044
  have eq156136 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq149730 (M.op (σ x) X0)
       have i₂ := eq28 (σ x) X0
       grind)
    | exact superpose eq28 eq149730
    | (have j0 := eq149730 (M.op (σ x) X0)
       grind)
    | exact resolve eq149730 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq149730
  have eq156212 : ∀ X0 : G, x = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq156136 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq156136
    | (have j0 := eq156136 X0
       grind)
    | exact resolve eq156136 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156136
  have eq162085 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x (τ (M.op (σ x) X0))
       have i₂ := eq156212 X0
       grind)
    | exact superpose eq156212 eq53
    | (have j0 := eq53 x (τ (M.op (σ x) X0))
       have j1 := eq156212 X0
       grind)
    | exact resolve eq53 eq156212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq156212
  have eq162095 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq162085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162085
  have eq260552 : ∀ X0 : G, (k (σ (M.op (τ X0) x)) X0) = X0 ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq100680 X0 x
       have i₂ := eq147655
       grind)
    | exact superpose eq147655 eq100680
    | exact resolve eq100680 eq147655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100680
  have eq260585 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq260552 (M.op (σ x) X0)
       have i₂ := eq162095 X0
       grind)
    | exact superpose eq162095 eq260552
    | (have j1 := eq162095 X0
       grind)
    | exact resolve eq260552 eq162095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162095 eq260552
  have eq260640 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq260585 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260585
  have eq269280 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq260640
  have eq269305 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq269280
       grind)
    | exact superpose eq269280 eq10
    | exact resolve eq10 eq269280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269280
  have eq269312 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq269305
  have eq269342 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq121353
       have i₂ := eq269312
       grind)
    | exact superpose eq269312 eq121353
    | exact resolve eq121353 eq269312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121353 eq269312
  have eq269742 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq269342
       have i₂ := eq147655
       grind)
    | exact superpose eq147655 eq269342
    | exact resolve eq269342 eq147655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147655 eq269342
  have eq269743 : False := by grind
  exact eq269743

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation2376 : Law3.StructuralFromFin Law2376 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V0_Equation2376
