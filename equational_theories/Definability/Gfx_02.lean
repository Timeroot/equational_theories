import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
