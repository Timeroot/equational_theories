import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation841`: `x = x ◇ ((y ◇ x) ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V1_Equation841 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law841 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law841.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = X0 := by
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
  have eq17 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X0 (M.op (M.op x X0) (M.op x x))
       have i₂ := eq8 X0 x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op x (M.op X0 X1)) (M.op x x)
       have i₂ := eq8 (M.op X0 X1) x x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X2 X1
       have i₂ := eq12 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq12 X0 (M.op (M.op X1 X0) (M.op X2 x))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X2 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
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
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq36 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (M.op X1 X0) X0
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq17
    | exact resolve eq17 eq18
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
    | (have i₁ := eq25 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq25 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq63 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq20 X1 (τ X0)
       grind)
    | exact superpose eq20 eq30
    | (have j0 := eq30 X0 X1
       have j1 := eq20 X1 (τ X0)
       grind)
    | exact resolve eq30 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
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
  clear eq30
  have eq75 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
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
  have eq80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
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
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36 (M.op X0 X2) (M.op X1 X0) X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq36
    | exact resolve eq36 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq36 X0 X0 X0
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (k (M.op X0 X1) X3) ∨ (M.op X1 X2) = (M.op (M.op X1 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 (M.op X0 X2) (M.op X1 X0)
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq23
    | (have j0 := eq23 X3 X1 X0
       grind)
    | exact resolve eq23 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq183 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq101 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq101
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq101 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq344 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
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
  clear eq33
  have eq543 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq183 X0 X1
       grind)
    | exact superpose eq183 eq53
    | (have j0 := eq53 X0 X1
       have j1 := eq183 X0 X1
       grind)
    | exact resolve eq53 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq550 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq543 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq658 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = X1 := by
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
  have eq734 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  clear eq90
  have eq761 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq1705 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
  have eq1768 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
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
  have eq1832 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ (M.op X1 X1)) X0) = (σ (M.op (M.op X1 X1) (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 X1 X1
       have i₂ := eq75 (M.op X1 X1) X0
       grind)
    | exact superpose eq75 eq36
    | (have j1 := eq75 (M.op X1 X1) X0
       grind)
    | exact resolve eq36 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1857 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = (σ (M.op (M.op X1 X1) (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1832 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832
  have eq3080 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq344
       have i₂ := eq26 y x
       grind)
    | exact superpose eq26 eq344
    | (have j1 := eq26 y x
       grind)
    | exact resolve eq344 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq344
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq344
    | (have j1 := eq53 y x
       grind)
    | exact resolve eq344 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq344
       have i₂ := eq550 y x
       grind)
    | exact superpose eq550 eq344
    | (have j1 := eq550 y x
       grind)
    | exact resolve eq344 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq3085 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq3083
  have eq3087 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq3081
  have eq3088 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3080
  have eq3364 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq3379 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3364 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3364
    | (have j0 := eq3364 X0 X1
       grind)
    | exact resolve eq3364 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq3381 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3379 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3379
    | (have j0 := eq3379 X0 X1
       grind)
    | exact resolve eq3379 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379
  have eq3382 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381
  have eq4263 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3088
  have eq6350 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq25 (σ x) (σ x)
       have i₂ := eq3087
       grind)
    | exact superpose eq3087 eq25
    | exact resolve eq25 eq3087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087
  have eq6498 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80 x (σ y)
       have i₂ := eq4263
       grind)
    | exact superpose eq4263 eq80
    | (have j0 := eq80 (k x (τ (σ y))) (σ y)
       grind)
    | exact resolve eq80 eq4263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4263
  have eq6517 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6498
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6498
    | exact resolve eq6498 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6498
  have eq6523 : x = y ∨ y = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6517
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6517
    | exact resolve eq6517 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6517
  have eq6524 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq6523
  have eq6683 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26 y x
       have i₂ := eq6524
       grind)
    | exact superpose eq6524 eq26
    | (have j0 := eq26 y x
       grind)
    | exact resolve eq26 eq6524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6524
  have eq6691 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq6683
  have eq6820 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36 x X0 y
       have i₂ := eq6691
       grind)
    | exact superpose eq6691 eq36
    | exact resolve eq36 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6691
  have eq20324 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1705 X0 X1
       grind)
    | exact superpose eq1705 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1705 X0 X1
       grind)
    | exact resolve eq13 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq20369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20324
  have eq21275 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq3382 X1 X0
       grind)
    | exact superpose eq3382 eq18
    | (have j1 := eq3382 X1 X0
       grind)
    | exact resolve eq18 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq26930 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0
       have i₂ := eq1768 (τ X0) X1
       grind)
    | exact superpose eq1768 eq62
    | (have j1 := eq1768 (τ X1) X0
       grind)
    | exact resolve eq62 eq1768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1768
  have eq26969 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq26930 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26930
  have eq27053 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X0) = (τ X1) ∨ (M.op (τ X1) (τ X0)) = (τ (k (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26969 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26969
    | (have j0 := eq26969 X0 X1
       grind)
    | exact resolve eq26969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26969
  have eq27083 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27053 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq27053
    | (have j0 := eq27053 X0 X1
       grind)
    | exact resolve eq27053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27053
  have eq28430 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18 (σ x) (σ x)
       have i₂ := eq3085
       grind)
    | exact superpose eq3085 eq18
    | exact resolve eq18 eq3085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq32393 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28430
       grind)
    | exact superpose eq28430 eq14
    | exact resolve eq14 eq28430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28430
  have eq36700 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X2 X0) X0) = (k (M.op X2 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq734 x X2
       have i₂ := eq178 X0 x X2 x
       grind)
    | exact superpose eq178 eq734
    | (have j1 := eq178 X2 X0 X2 X0
       grind)
    | exact resolve eq734 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq734
  have eq36795 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k (M.op X2 X0) X0) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36700 X0 X1 X2
       have i₂ := eq25 X0 X2
       grind)
    | exact superpose eq25 eq36700
    | (have j0 := eq36700 X0 X1 X2
       grind)
    | exact resolve eq36700 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36700
  have eq59300 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq761 X0
       have i₂ := eq658 (σ X0) X1
       grind)
    | exact superpose eq658 eq761
    | (have j1 := eq658 (σ X1) X0
       grind)
    | exact resolve eq761 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq761
  have eq59545 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59300 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59300
    | (have j0 := eq59300 X0 X1
       grind)
    | exact resolve eq59300 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59300
  have eq59597 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59545 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59545
    | (have j0 := eq59545 X0 X1
       grind)
    | exact resolve eq59545 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59545
  have eq59631 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59597 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq59597
    | (have j0 := eq59597 X0 X1
       grind)
    | exact resolve eq59597 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59597
  have eq59642 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59631 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq59631
    | (have j0 := eq59631 X0 X1
       grind)
    | exact resolve eq59631 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59631
  have eq59643 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq59642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59642
  have eq92913 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21275 X0 X1
       have i₂ := eq20369 X0 X1
       grind)
    | exact superpose eq20369 eq21275
    | (have j0 := eq21275 X0 X1
       have j1 := eq20369 X0 X1
       grind)
    | exact resolve eq21275 eq20369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20369
  have eq93207 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq92913 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92913
  have eq103748 : (τ (σ y)) = (k y x) ∨ x = y ∨ x = (k y x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq59643 x y
       have i₂ := eq6350
       grind)
    | exact superpose eq6350 eq59643
    | (have j0 := eq59643 x y
       grind)
    | exact resolve eq59643 eq6350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6350 eq59643
  have eq103842 : (τ (σ y)) = (k y x) ∨ x = y ∨ x = (k y x) ∨ y = (M.op y x) := by grind
  clear eq103748
  have eq103878 : y = (k y x) ∨ x = y ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq103842
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq103842
    | exact resolve eq103842 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103842
  have eq137503 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq103878
       have i₂ := eq26 x y
       grind)
    | exact superpose eq26 eq103878
    | (have j1 := eq26 x y
       grind)
    | exact resolve eq103878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq103878
  have eq137564 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq137503
  have eq138392 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18 y x
       have i₂ := eq137564
       grind)
    | exact superpose eq137564 eq18
    | exact resolve eq18 eq137564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137564
  have eq139080 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6820 y
       have i₂ := eq138392
       grind)
    | exact superpose eq138392 eq6820
    | exact resolve eq6820 eq138392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6820 eq138392
  have eq139203 : x = (M.op x y) ∨ x = y := by grind
  clear eq139080
  have eq139807 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq32393
       have i₂ := eq139203
       grind)
    | exact superpose eq139203 eq32393
    | exact resolve eq32393 eq139203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32393
  have eq139820 : y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq139203
       grind)
    | exact superpose eq139203 eq18
    | exact resolve eq18 eq139203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139964 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq139807
  have eq139965 : y = (M.op y y) ∨ x = y := by grind
  clear eq139964
  have eq140703 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq93207 y x
       have i₂ := eq139820
       grind)
    | exact superpose eq139820 eq93207
    | (have j0 := eq93207 y x
       grind)
    | exact resolve eq93207 eq139820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93207
  have eq140704 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = y := by grind
  clear eq140703
  have eq141559 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq100 y x
       have i₂ := eq139965
       grind)
    | exact superpose eq139965 eq100
    | exact resolve eq100 eq139965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq139965
  have eq211447 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq140704
       grind)
    | exact superpose eq140704 eq14
    | exact resolve eq14 eq140704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140704
  have eq213083 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq211447
       have i₂ := eq139203
       grind)
    | exact superpose eq139203 eq211447
    | exact resolve eq211447 eq139203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139203 eq211447
  have eq213100 : (σ x) ≠ (σ x) ∨ x = (k y x) ∨ x = y := by grind
  clear eq213083
  have eq213101 : x = (k y x) ∨ x = y := by grind
  clear eq213100
  have eq213346 : x = (M.op y x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq141559 x
       have i₂ := eq213101
       grind)
    | exact superpose eq213101 eq141559
    | (have j0 := eq141559 x
       grind)
    | exact resolve eq141559 eq213101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141559 eq213101
  have eq213445 : x = (M.op y x) ∨ x = y := by grind
  clear eq213346
  have eq213907 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq139820
       have i₂ := eq213445
       grind)
    | exact superpose eq213445 eq139820
    | exact resolve eq139820 eq213445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139820 eq213445
  have eq214180 : x = y := by grind
  clear eq213907
  have eq215554 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq214180
       grind)
    | exact superpose eq214180 eq14
    | exact resolve eq14 eq214180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214180
  have eq221945 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq215554
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq215554
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq215554
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq215554
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq215554 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221946 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq215554
       have i₂ := eq550 (σ x) X0
       grind)
    | exact superpose eq550 eq215554
    | (have j1 := eq550 (σ x) X0
       grind)
    | exact resolve eq215554 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260255 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq221945 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221945
  have eq260710 : (τ (M.op (σ x) (σ (M.op x x)))) = (k (τ (σ x)) (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq67 (σ x) (M.op x x)
       have i₂ := eq260255
       grind)
    | exact superpose eq260255 eq67
    | (have j0 := eq67 (M.op (σ x) (σ (M.op x x))) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq67 eq260255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260255
  have eq260712 : (k x (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq260710
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq260710
    | exact resolve eq260710 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260710
  have eq260717 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq260712
  have eq260719 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq260717
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq260717
    | exact resolve eq260717 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260717
  have eq787725 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (k X0 X1))) ∨ (k X0 X1) = X1 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (τ X0) (τ X1)
       have i₂ := eq27083 X1 X0
       grind)
    | exact superpose eq27083 eq18
    | (have j1 := eq27083 X1 X0
       grind)
    | exact resolve eq18 eq27083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27083
  have eq852836 : ∀ X0 X3 : G, (M.op X3 X0) = (k (M.op X3 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq36795 x (M.op (M.op x x) X0) x
       have i₂ := eq17 X0 x x
       grind)
    | exact superpose eq17 eq36795
    | (have j0 := eq36795 X0 x X3
       grind)
    | exact resolve eq36795 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq36795
  have eq855018 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21275 (M.op x X0) X0
       have i₂ := eq852836 X0 x
       grind)
    | exact superpose eq852836 eq21275
    | (have j0 := eq21275 X1 X1
       have j1 := eq852836 X1 x
       grind)
    | exact resolve eq21275 eq852836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21275 eq852836
  have eq855052 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq855018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855018
  have eq890151 : ∀ X0 X1 : G, (M.op X0 (τ (k X1 (σ X0)))) = X0 ∨ (σ X0) = (k X1 (σ X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq787725 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq787725
    | (have j0 := eq787725 X1 (σ X0)
       grind)
    | exact resolve eq787725 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787725
  have eq930013 : ∀ X0 X1 : G, (M.op X1 (k (τ X0) X1)) = X1 ∨ (σ X1) = (k X0 (σ X1)) ∨ (τ X0) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq890151 X1 X0
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq890151
    | (have j0 := eq890151 X1 X0
       have j1 := eq67 X0 X1
       grind)
    | exact resolve eq890151 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890151
  have eq930202 : ∀ X0 X1 : G, (M.op X1 (k (τ X0) X1)) = X1 ∨ (σ X1) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq930013 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930013
  have eq935980 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (M.op X1 (k X0 X1)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq930202 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq930202
    | (have j0 := eq930202 (σ X0) X1
       grind)
    | exact resolve eq930202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930202
  have eq1047888 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq260719
       have i₂ := eq855052 x x
       grind)
    | exact superpose eq855052 eq260719
    | (have j1 := eq855052 x x
       grind)
    | exact resolve eq260719 eq855052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260719 eq855052
  have eq1047960 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq1047888
  have eq1047972 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1047960
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1047960
    | exact resolve eq1047960 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047960
  have eq1047973 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq1047972
  have eq1048037 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq550 x x
       have i₂ := eq1047973
       grind)
    | exact superpose eq1047973 eq550
    | (have j0 := eq550 x x
       grind)
    | exact resolve eq550 eq1047973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq1047973
  have eq1048050 : x = (M.op x x) := by grind
  clear eq1048037
  have eq1048119 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq221946 X0
       have i₂ := eq1048050
       grind)
    | exact superpose eq1048050 eq221946
    | (have j0 := eq221946 X0
       grind)
    | exact resolve eq221946 eq1048050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221946
  have eq1048229 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq1857 X0 x
       have i₂ := eq1048050
       grind)
    | exact superpose eq1048050 eq1857
    | exact resolve eq1857 eq1048050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq1048545 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq1048119 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048119
  have eq1050620 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq67 X0 x
       have i₂ := eq1048545 X0
       grind)
    | exact superpose eq1048545 eq67
    | (have j0 := eq67 (M.op X0 (σ x)) (k (τ X0) x)
       grind)
    | exact resolve eq67 eq1048545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1050752 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq935980 X0 x
       have i₂ := eq1048545 (σ X0)
       grind)
    | exact superpose eq1048545 eq935980
    | (have j0 := eq935980 X0 x
       grind)
    | exact resolve eq935980 eq1048545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935980 eq1048545
  have eq1085059 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ (M.op X0 (σ x))) x) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1050620 (M.op X0 (σ x))
       have i₂ := eq25 (σ x) X0
       grind)
    | exact superpose eq25 eq1050620
    | (have j0 := eq1050620 (M.op X0 (σ x))
       grind)
    | exact resolve eq1050620 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050620
  have eq1176310 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq25 (σ x) (σ X0)
       have i₂ := eq1050752 X0
       grind)
    | exact superpose eq1050752 eq25
    | (have j1 := eq1050752 X0
       grind)
    | exact resolve eq25 eq1050752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1050752
  have eq1196196 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq215554
       have i₂ := eq1176310 X0
       grind)
    | exact superpose eq1176310 eq215554
    | (have j1 := eq1176310 X0
       grind)
    | exact resolve eq215554 eq1176310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176310
  have eq1196376 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq1196196 X0
       have i₂ := eq1048050
       grind)
    | exact superpose eq1048050 eq1196196
    | (have j0 := eq1196196 X0
       grind)
    | exact resolve eq1196196 eq1048050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196196
  have eq1196377 : ∀ X0 : G, x = (M.op x (k X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq1196376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196376
  have eq1410280 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1196377 (τ (M.op X0 (σ x)))
       have i₂ := eq1085059 X0
       grind)
    | exact superpose eq1085059 eq1196377
    | (have j0 := eq1196377 (M.op x (τ (M.op X0 (σ x))))
       have j1 := eq1085059 X0
       grind)
    | exact resolve eq1196377 eq1085059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085059 eq1196377
  have eq1410281 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq1410280 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410280
  have eq1410381 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1048229 (M.op X0 (σ x))
       have i₂ := eq1410281 X0
       grind)
    | exact superpose eq1410281 eq1048229
    | (have j0 := eq1048229 (M.op X0 (σ x))
       have j1 := eq1410281 X0
       grind)
    | exact resolve eq1048229 eq1410281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048229 eq1410281
  have eq1410670 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq1410381 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410381
  have eq1411118 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1410670
  have eq1411717 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq1411118
       grind)
    | exact superpose eq1411118 eq10
    | exact resolve eq10 eq1411118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411118
  have eq1411718 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1411717
  have eq1411752 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq215554
       have i₂ := eq1411718
       grind)
    | exact superpose eq1411718 eq215554
    | exact resolve eq215554 eq1411718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215554 eq1411718
  have eq1412219 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1411752
       have i₂ := eq1048050
       grind)
    | exact superpose eq1048050 eq1411752
    | exact resolve eq1411752 eq1048050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048050 eq1411752
  have eq1412220 : False := by grind
  exact eq1412220

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation841 : Law3.StructuralFromFin Law841 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V1_Equation841

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V1_Equation854 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
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
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq16
    | exact resolve eq16 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op X2 (M.op (M.op X0 X1) X1)) X0 X1
       have i₂ := eq8 (M.op X0 X1) X2 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq8 eq16
    | exact resolve eq16 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X0 (M.op (M.op X3 X4) (M.op X2 X4))))) X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X1 (M.op X2 (M.op X0 (M.op (M.op X3 X4) (M.op X2 X4))))
       have i₂ := eq16 X2 X0 X3 X4
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq59 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq59
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq8
    | exact resolve eq8 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X0 X1) X0 X1
       have i₂ := eq59 (M.op X0 X1)
       grind)
    | exact superpose eq59 eq17
    | exact resolve eq17 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))) (M.op X0 X4)) ∨ (k (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))) X4) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X4 (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))) X0
       have i₂ := eq16 X1 X0 X2 X3
       grind)
    | exact superpose eq16 eq20
    | (have j0 := eq20 X4 (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))) X2
       grind)
    | exact resolve eq20 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq120 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0 x X0
       have i₂ := eq20 (M.op X1 X0) X0 x
       grind)
    | exact superpose eq20 eq17
    | (have j1 := eq20 (M.op X1 X0) X0 x
       grind)
    | exact resolve eq17 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq188 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (M.op X1 X0)
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq71
    | exact resolve eq71 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq231 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X1 X0
       have i₂ := eq188 X1 X0
       grind)
    | exact superpose eq188 eq20
    | (have j0 := eq20 X1 X1 x
       grind)
    | exact resolve eq20 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq233 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X1) X2 X1
       have i₂ := eq188 X1 X0
       grind)
    | exact superpose eq188 eq8
    | exact resolve eq8 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X1) X1
       have i₂ := eq188 X1 X0
       grind)
    | exact superpose eq188 eq24
    | (have j0 := eq24 X0 X1
       grind)
    | exact resolve eq24 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq65 (σ X1) (σ X0)
       grind)
    | exact superpose eq65 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       have j1 := eq65 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
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
  clear eq30
  have eq330 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39
    | (have j0 := eq39 (k X1 X0) (k (τ X1) (τ X0))
       grind)
    | exact resolve eq39 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq39
    | (have j0 := eq39 (M.op X0 (σ X1)) (k (τ X0) X1)
       have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq241 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq241
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq241 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq241 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq241 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq446 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 X0
       have i₂ := eq120 X1 X0
       grind)
    | exact superpose eq120 eq21
    | (have j0 := eq21 (M.op X0 X1) X1 X1
       have j1 := eq120 X1 X0
       grind)
    | exact resolve eq21 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1098 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 X0
       have i₂ := eq231 X1 X0
       grind)
    | exact superpose eq231 eq21
    | (have j0 := eq21 X0 X1 X0
       have j1 := eq231 X0 X0
       grind)
    | exact resolve eq21 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1135 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1098 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1277 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq1135 X1 X0
       grind)
    | exact superpose eq1135 eq231
    | (have j0 := eq231 X0 X1
       have j1 := eq1135 X0 X1
       grind)
    | exact resolve eq231 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq1135
  have eq1318 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1477 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 X0 x x x
       have i₂ := eq1318 (M.op x (M.op X1 (M.op (M.op x x) (M.op x x)))) X0
       grind)
    | exact superpose eq1318 eq63
    | (have j1 := eq1318 (M.op X0 X1) X1
       grind)
    | exact resolve eq63 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1318
  have eq1789 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X1 (M.op X0 X1)
       have i₂ := eq1477 X0 X1
       grind)
    | exact superpose eq1477 eq241
    | (have j0 := eq241 X1 X0
       have j1 := eq1477 X1 X1
       grind)
    | exact resolve eq241 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq4398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq286
       have i₂ := eq19 y x
       grind)
    | exact superpose eq19 eq286
    | (have j1 := eq19 y x
       grind)
    | exact resolve eq286 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq286
  have eq4406 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq4398
  have eq4460 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq4406
  have eq6224 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6288 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq47 x (σ y)
       have i₂ := eq4460
       grind)
    | exact superpose eq4460 eq47
    | (have j0 := eq47 (k x (τ (σ y))) (σ y)
       grind)
    | exact resolve eq47 eq4460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4460
  have eq6300 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq6288
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6288
    | exact resolve eq6288 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288
  have eq6301 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y := by grind
  clear eq6300
  have eq6305 : x = y ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq6301
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6301
    | exact resolve eq6301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6301
  have eq6306 : y = (k x y) ∨ x = y := by grind
  clear eq6305
  have eq6683 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6306
       grind)
    | exact superpose eq6306 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6306
  have eq7029 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 y) y)) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 x X0 y
       have i₂ := eq6683
       grind)
    | exact superpose eq6683 eq8
    | exact resolve eq8 eq6683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7071 : y = (M.op y y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq188 y x
       have i₂ := eq6683
       grind)
    | exact superpose eq6683 eq188
    | exact resolve eq188 eq6683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7092 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq7029 X0
       have i₂ := eq188 y X0
       grind)
    | exact superpose eq188 eq7029
    | exact resolve eq7029 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7029
  have eq11474 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7092 y
       have i₂ := eq7071
       grind)
    | exact superpose eq7071 eq7092
    | exact resolve eq7092 eq7071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7071 eq7092
  have eq11582 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq11474
  have eq11960 : x = y ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq6683
       have i₂ := eq11582
       grind)
    | exact superpose eq11582 eq6683
    | exact resolve eq6683 eq11582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6683 eq11582
  have eq12036 : y = (M.op x x) ∨ x = y := by grind
  clear eq11960
  have eq12464 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq59
    | exact resolve eq59 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49559 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) = X3 ∨ (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) X3) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) X3) ∨ (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) X3
       have i₂ := eq107 X0 X0 X1 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))
       grind)
    | exact superpose eq107 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) X3
       have j1 := eq107 X0 X0 X1 X2 X3
       grind)
    | exact resolve eq12 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq49700 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X3 ∨ (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) X3) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) X3) ∨ (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49559 X0 X1 X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq49559
    | (have j0 := eq49559 X0 X1 X2 X3
       grind)
    | exact resolve eq49559 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49559
  have eq49725 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X3) = (k (M.op X0 X0) X3) ∨ (M.op X0 X0) = X3 ∨ (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49700 X0 X1 X2 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq49700
    | (have j0 := eq49700 X0 X1 X2 X3
       grind)
    | exact resolve eq49700 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49700
  have eq49739 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) = (k (M.op X0 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) ∨ (M.op (M.op X0 X0) X3) = (k (M.op X0 X0) X3) ∨ (M.op X0 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49725 X0 X1 X2 X3
       have i₂ := eq188 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) X0
       grind)
    | exact superpose eq188 eq49725
    | (have j0 := eq49725 X0 X1 X2 X3
       grind)
    | exact resolve eq49725 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49725
  have eq49746 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = (k (M.op X0 X0) X3) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq49739 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq49739
    | (have j0 := eq49739 X0 x x X3
       grind)
    | exact resolve eq49739 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49739
  have eq51261 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq6224 x
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq6224
    | exact resolve eq6224 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51333 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq51261
  have eq51439 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq51333
       grind)
    | exact superpose eq51333 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq51333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83180 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0
       have i₂ := eq339 (σ X0) X1
       grind)
    | exact superpose eq339 eq364
    | (have j1 := eq339 (σ X1) X0
       grind)
    | exact resolve eq364 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq83369 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83180 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq83180
    | (have j0 := eq83180 X0 X1
       grind)
    | exact resolve eq83180 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83180
  have eq83401 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83369 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq83369
    | (have j0 := eq83369 X0 X1
       grind)
    | exact resolve eq83369 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83369
  have eq83417 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83401 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq83401
    | (have j0 := eq83401 X0 X1
       grind)
    | exact resolve eq83401 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83401
  have eq83426 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83417 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq83417
    | (have j0 := eq83417 X0 X1
       grind)
    | exact resolve eq83417 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83417
  have eq83427 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq83426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83426
  have eq83868 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq446 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq446
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq446 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq84183 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83868 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83868
  have eq84294 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 X0
       have i₂ := eq84183 (τ X1) X0
       grind)
    | exact superpose eq84183 eq26
    | (have j0 := eq26 X1 X0
       have j1 := eq84183 (τ X1) X0
       grind)
    | exact resolve eq26 eq84183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq84183
  have eq84465 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq84294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84294
  have eq99265 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq49746 X0 (k (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49746
  have eq99266 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq99265 X0
       grind)
    | (have r₁ := eq99265 X0
       have r₂ := eq188 X0 X0
       grind)
    | exact resolve eq99265 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99265
  have eq99267 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99266 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq99266 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq99266
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq99266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99292 : y = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq99266 x
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq99266
    | exact resolve eq99266 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036 eq99266
  have eq99354 : y = (k y x) ∨ x = y := by grind
  clear eq99292
  have eq99623 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq99267 (τ X0) X1
       grind)
    | exact superpose eq99267 eq25
    | (have j0 := eq25 X0 X1
       have j1 := eq99267 (τ X0) X1
       grind)
    | exact resolve eq25 eq99267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq99635 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq99623 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99623
  have eq99675 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99635 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99635
    | (have j0 := eq99635 X0 X1
       grind)
    | exact resolve eq99635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99635
  have eq128781 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99675 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99675
    | (have j0 := eq99675 (σ X0) X1
       grind)
    | exact resolve eq99675 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99675
  have eq129013 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X1) (σ X0)
       have i₂ := eq128781 X0 X1
       grind)
    | exact superpose eq128781 eq65
    | (have j0 := eq65 X0 X1
       have j1 := eq128781 X0 X1
       grind)
    | exact resolve eq65 eq128781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq128781
  have eq129015 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq129013 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129013
  have eq129108 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83427 X1 X0
       have i₂ := eq129015 X0 X1
       grind)
    | exact superpose eq129015 eq83427
    | (have j0 := eq83427 (τ (σ X0)) (k X0 X1)
       have j1 := eq129015 X0 X1
       grind)
    | exact resolve eq83427 eq129015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129015
  have eq129156 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq129108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129108
  have eq129171 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq129156 X0 X1
       have j1 := eq355 X0 X1
       grind)
    | (have r₁ := eq129156 X0 X1
       have r₂ := eq355 (τ (σ X0)) (k X0 X1)
       grind)
    | (have r₁ := eq129156 X0 X1
       have r₂ := eq355 (k X0 X1) (τ (σ X0))
       grind)
    | (have r₁ := eq129156 X0 X1
       have r₂ := eq355 X0 X1
       grind)
    | exact resolve eq129156 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq129156
  have eq129173 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq129171 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq129171
    | (have j0 := eq129171 X0 X1
       grind)
    | exact resolve eq129171 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129171
  have eq129363 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq129173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129173
  have eq129434 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq129363 X0 X1
       have j1 := eq99267 X0 X1
       grind)
    | (have r₁ := eq129363 (k X1 X0) (M.op X1 X0)
       have r₂ := eq99267 X0 X1
       grind)
    | (have r₁ := eq129363 (M.op X1 X0) (k X1 X0)
       have r₂ := eq99267 X0 X1
       grind)
    | (have r₁ := eq129363 (k X0 X1) X0
       have r₂ := eq99267 X0 X1
       grind)
    | exact resolve eq129363 eq99267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99267 eq129363
  have eq129620 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (τ X1) = X0 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq129434 (σ X0) X1
       grind)
    | exact superpose eq129434 eq47
    | (have j0 := eq47 (k X0 (τ X1)) (σ X0)
       have j1 := eq129434 (σ X0) X1
       grind)
    | exact resolve eq47 eq129434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq129434
  have eq129783 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq129620 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq129620
    | (have j0 := eq129620 X0 X1
       grind)
    | exact resolve eq129620 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129620
  have eq140830 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq84 (σ x) (σ y)
       have i₂ := eq51439
       grind)
    | exact superpose eq51439 eq84
    | exact resolve eq84 eq51439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq51439
  have eq143066 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X1 X0
       have i₂ := eq129783 (τ X0) X1
       grind)
    | exact superpose eq129783 eq330
    | (have j0 := eq330 X0 (k X0 X1)
       have j1 := eq129783 (τ X0) X1
       grind)
    | exact resolve eq330 eq129783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq129783
  have eq143068 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq143066 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143066
  have eq143075 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq143068 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq143068
    | (have j0 := eq143068 X0 X1
       grind)
    | exact resolve eq143068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143068
  have eq149660 : (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq143075 (σ x) (σ y)
       have i₂ := eq51333
       grind)
    | exact superpose eq51333 eq143075
    | (have j0 := eq143075 (σ x) (σ y)
       grind)
    | exact resolve eq143075 eq51333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51333 eq143075
  have eq149680 : (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq149660
  have eq149685 : y = (τ (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq149680
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq149680
    | exact resolve eq149680 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149680
  have eq149687 : x = y ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq149685
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq149685
    | exact resolve eq149685 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149685
  have eq149688 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq149687
  have eq149705 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq149688
       grind)
    | exact superpose eq149688 eq13
    | (have j0 := eq13 (M.op (σ y) (σ x)) (σ (k y x))
       grind)
    | exact resolve eq13 eq149688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149688
  have eq149742 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = y := by grind
  clear eq149705
  have eq149862 : (σ (k y x)) = (M.op (σ (k y x)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq188 (σ x) (σ y)
       have i₂ := eq149742
       grind)
    | exact superpose eq149742 eq188
    | exact resolve eq188 eq149742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149742
  have eq150048 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq149862
       have i₂ := eq99354
       grind)
    | exact superpose eq99354 eq149862
    | exact resolve eq149862 eq99354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99354 eq149862
  have eq150216 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq150048
  have eq150309 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ x))) = (M.op (M.op X0 (M.op (σ y) (σ x))) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 (σ y) (σ x) x
       have i₂ := eq150216
       grind)
    | exact superpose eq150216 eq61
    | exact resolve eq61 eq150216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq150216
  have eq260125 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ X0 = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq382245 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq150309 (σ x)
       have i₂ := eq140830
       grind)
    | exact superpose eq140830 eq150309
    | exact resolve eq150309 eq140830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140830 eq150309
  have eq382249 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq382245
  have eq382251 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq382249
       grind)
    | exact superpose eq382249 eq14
    | exact resolve eq14 eq382249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382249
  have eq382256 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq382251
       have i₂ := eq12464
       grind)
    | exact superpose eq12464 eq382251
    | exact resolve eq382251 eq12464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382251
  have eq382257 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq382256
  have eq382258 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq382257
  have eq382341 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq59 (σ x)
       have i₂ := eq382258
       grind)
    | exact superpose eq382258 eq59
    | exact resolve eq59 eq382258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq382258
  have eq382613 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq382341
       grind)
    | exact superpose eq382341 eq14
    | exact resolve eq14 eq382341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382341
  have eq382836 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq382613
       have i₂ := eq12464
       grind)
    | exact superpose eq12464 eq382613
    | exact resolve eq382613 eq12464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464 eq382613
  have eq382871 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq382836
  have eq382872 : x = y := by grind
  clear eq382871
  have eq382873 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq382872
       grind)
    | exact superpose eq382872 eq14
    | exact resolve eq14 eq382872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382872
  have eq382912 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq382873
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq382873
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq382873
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq382873
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq382873 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384355 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq382912 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382912
  have eq384451 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6224 x
       have i₂ := eq384355
       grind)
    | exact superpose eq384355 eq6224
    | (have j0 := eq6224 x
       grind)
    | exact resolve eq6224 eq384355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224
  have eq384454 : (k (τ (σ x)) (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq39 (σ x) (M.op x x)
       have i₂ := eq384355
       grind)
    | exact superpose eq384355 eq39
    | (have j0 := eq39 (M.op (σ x) (σ (M.op x x))) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq39 eq384355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384355
  have eq384455 : (k x (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq384454
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq384454
    | exact resolve eq384454 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384454
  have eq384459 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq384455
  have eq384461 : (M.op x x) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq384459
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq384459
    | exact resolve eq384459 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384459
  have eq386282 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ (M.op x x))) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) X0 (σ (M.op x x))
       have i₂ := eq384451
       grind)
    | exact superpose eq384451 eq8
    | exact resolve eq8 eq384451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386290 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq386282 X0
       have i₂ := eq188 (σ (M.op x x)) X0
       grind)
    | exact superpose eq188 eq386282
    | exact resolve eq386282 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386282
  have eq386360 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq386290 (σ x)
       have i₂ := eq384451
       grind)
    | exact superpose eq384451 eq386290
    | exact resolve eq386290 eq384451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384451 eq386290
  have eq386568 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by grind
  clear eq386360
  have eq386635 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq384461
       have i₂ := eq386568
       grind)
    | exact superpose eq386568 eq384461
    | exact resolve eq384461 eq386568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384461 eq386568
  have eq386658 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq386635
  have eq386663 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq386658
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq386658
    | exact resolve eq386658 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386658
  have eq386664 : x = (M.op x x) := by grind
  clear eq386663
  have eq387313 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq386664
       grind)
    | exact superpose eq386664 eq8
    | exact resolve eq8 eq386664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387393 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq233 x x x
       have i₂ := eq386664
       grind)
    | exact superpose eq386664 eq233
    | exact resolve eq233 eq386664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq387479 : x ≠ x ∨ x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1789 x x
       have i₂ := eq386664
       grind)
    | exact superpose eq386664 eq1789
    | (have r₁ := eq1789 x x
       have r₂ := eq386664
       grind)
    | exact resolve eq1789 eq386664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq386664
  have eq387732 : x ≠ x ∨ x = (k x x) := by grind
  clear eq387479
  have eq387733 : x = (k x x) := by grind
  clear eq387732
  have eq387818 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq387393 X0
       have i₂ := eq188 x X0
       grind)
    | exact superpose eq188 eq387393
    | exact resolve eq387393 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq387393
  have eq390033 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq387313 X0
       have i₂ := eq387818 X0
       grind)
    | exact superpose eq387818 eq387313
    | exact resolve eq387313 eq387818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387313
  have eq390915 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq387818 X0
       have i₂ := eq390033 X0
       grind)
    | exact superpose eq390033 eq387818
    | exact resolve eq387818 eq390033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387818
  have eq393670 : ∀ X0 : G, x ≠ X0 ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq241 x X0
       have i₂ := eq390915 X0
       grind)
    | exact superpose eq390915 eq241
    | (have r₁ := eq241 x x
       have r₂ := eq390915 x
       grind)
    | exact resolve eq241 eq390915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq398099 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (τ X0) = (k x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq84465 x X0
       have i₂ := eq390915 (τ X0)
       grind)
    | exact superpose eq390915 eq84465
    | (have j0 := eq84465 x X0
       grind)
    | exact resolve eq84465 eq390915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84465 eq390915
  have eq398495 : ∀ X0 : G, (τ X0) = x ∨ (σ x) = (k (σ x) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq398099 X0
       have i₂ := eq387733
       grind)
    | exact superpose eq387733 eq398099
    | (have j0 := eq398099 X0
       grind)
    | exact resolve eq398099 eq387733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387733 eq398099
  have eq398496 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq398495 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398495
  have eq418456 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq39 (σ x) X0
       have i₂ := eq398496 (σ X0)
       grind)
    | exact superpose eq398496 eq39
    | (have j0 := eq39 (σ x) (k (τ (σ x)) X0)
       have j1 := eq398496 (σ X0)
       grind)
    | exact resolve eq39 eq398496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq398496
  have eq418465 : ∀ X0 : G, x = (k x X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq418456 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq418456
    | (have j0 := eq418456 X0
       grind)
    | exact resolve eq418456 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418456
  have eq418477 : ∀ X0 : G, x = X0 ∨ x = (k x X0) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq418465 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq418465
    | (have j0 := eq418465 X0
       grind)
    | exact resolve eq418465 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418465
  have eq418479 : ∀ X0 : G, x = X0 ∨ x = X0 ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq418477 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq418477
    | (have j0 := eq418477 X0
       grind)
    | exact resolve eq418477 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418477
  have eq418480 : ∀ X0 : G, x = (k x X0) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq418479 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418479
  have eq418613 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = X0 ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq260125 x X0
       have i₂ := eq418480 X0
       grind)
    | exact superpose eq418480 eq260125
    | (have j0 := eq260125 x X0
       have j1 := eq418480 X0
       grind)
    | exact resolve eq260125 eq418480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260125
  have eq418632 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = X0 ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq418613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418613
  have eq418633 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq418632 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418632
  have eq426910 : ∀ X0 : G, (k x X0) = (τ (σ x)) ∨ x = X0 ∨ (k x X0) = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq83427 X0 x
       have i₂ := eq418633 X0
       grind)
    | exact superpose eq418633 eq83427
    | (have j0 := eq83427 (k x X0) (τ (σ x))
       have j1 := eq418633 X0
       grind)
    | exact resolve eq83427 eq418633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83427 eq418633
  have eq426966 : ∀ X0 : G, (k x X0) = (τ (σ x)) ∨ x = X0 ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq426910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426910
  have eq426992 : ∀ X0 : G, (k x X0) = (τ (σ x)) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq426966 X0
       have j1 := eq393670 X0
       grind)
    | (have r₁ := eq426966 X0
       have r₂ := eq393670 X0
       grind)
    | (have r₁ := eq426966 x
       have r₂ := eq393670 x
       grind)
    | (have r₁ := eq426966 x
       have r₂ := eq393670 (k x x)
       grind)
    | exact resolve eq426966 eq393670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393670 eq426966
  have eq426996 : ∀ X0 : G, x = (k x X0) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq426992 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq426992
    | (have j0 := eq426992 X0
       grind)
    | exact resolve eq426992 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426992
  have eq427160 : ∀ X0 : G, x ≠ X0 ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq426996 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426996
  have eq427213 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq427160 X0
       have j1 := eq418480 X0
       grind)
    | (have r₁ := eq427160 (k x X0)
       have r₂ := eq418480 X0
       grind)
    | (have r₁ := eq427160 X0
       have r₂ := eq418480 X0
       grind)
    | (have r₁ := eq427160 x
       have r₂ := eq418480 x
       grind)
    | exact resolve eq427160 eq418480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418480 eq427160
  have eq427763 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq364 x
       have i₂ := eq427213 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq427213 eq364
    | (have j0 := eq364 x
       grind)
    | exact resolve eq364 eq427213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq427213
  have eq427776 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq427763
  have eq427949 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq427776
       grind)
    | exact superpose eq427776 eq10
    | exact resolve eq10 eq427776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427776
  have eq428063 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq382873
       have i₂ := eq427949
       grind)
    | exact superpose eq427949 eq382873
    | exact resolve eq382873 eq427949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382873 eq427949
  have eq428188 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq428063
       have i₂ := eq390033 x
       grind)
    | exact superpose eq390033 eq428063
    | exact resolve eq428063 eq390033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390033 eq428063
  have eq428189 : False := by grind
  exact eq428189

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation854 : Law3.StructuralFromFin Law854 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V1_Equation854

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V1_Equation1043 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1043 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 (M.op X0 X2)) X0 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | (have j1 := eq24 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | (have j1 := eq25 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq16 X0 X1 X3 X4
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq58
    | exact resolve eq58 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq169 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq201 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq29 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq29 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq273 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 x X0
       have i₂ := eq65 X0 X0 x
       grind)
    | exact superpose eq65 eq16
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0 X0 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq65
    | exact resolve eq65 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq362 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq65
    | exact resolve eq65 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq378 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq17 X0 X1 X0
       grind)
    | exact superpose eq17 eq372
    | exact resolve eq372 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq372
  have eq1003 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X0) (M.op X0 X0)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq378 X0 X1
       grind)
    | exact superpose eq378 eq16
    | exact resolve eq16 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq1004 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq378 X0 X1
       grind)
    | exact superpose eq378 eq8
    | exact resolve eq8 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1004 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq1004
    | exact resolve eq1004 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1027 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1003 X0 X1 X2
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq1003
    | exact resolve eq1003 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq1003
  have eq1031 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X1)) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1027 x X1 X2
       have i₂ := eq1026 x (M.op X2 X1)
       grind)
    | exact superpose eq1026 eq1027
    | exact resolve eq1027 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1181 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X1 X0
       have i₂ := eq1026 X1 X0
       grind)
    | exact superpose eq1026 eq378
    | exact resolve eq378 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq1248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq201
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq201
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq201 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq201
       have i₂ := eq19 y x
       grind)
    | exact superpose eq19 eq201
    | (have j1 := eq19 y x
       grind)
    | exact resolve eq201 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq201
  have eq1259 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq1251
  have eq1262 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq1248
  have eq7257 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq1259
  have eq8200 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1026 (σ x) X0
       have i₂ := eq1262
       grind)
    | exact superpose eq1262 eq1026
    | exact resolve eq1026 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq8649 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq8200 (σ x)
       grind)
    | exact superpose eq8200 eq14
    | exact resolve eq14 eq8200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8200
  have eq12174 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq46 x (σ y)
       have i₂ := eq7257
       grind)
    | exact superpose eq7257 eq46
    | (have j0 := eq46 (k x (τ (σ y))) (σ y)
       grind)
    | exact resolve eq46 eq7257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq7257
  have eq12196 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq12174
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq12174
    | exact resolve eq12174 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12174
  have eq12197 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y := by grind
  clear eq12196
  have eq12205 : x = y ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq12197
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq12197
    | exact resolve eq12197 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12197
  have eq12206 : y = (k x y) ∨ x = y := by grind
  clear eq12205
  have eq12699 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq12206
       grind)
    | exact superpose eq12206 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq12206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12206
  have eq13052 : y = (M.op y y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1031 y x
       have i₂ := eq12699
       grind)
    | exact superpose eq12699 eq1031
    | exact resolve eq1031 eq12699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq12699
  have eq13331 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1026 y X0
       have i₂ := eq13052
       grind)
    | exact superpose eq13052 eq1026
    | exact resolve eq1026 eq13052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13052
  have eq14965 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq8649
       have i₂ := eq13331 x
       grind)
    | exact superpose eq13331 eq8649
    | exact resolve eq8649 eq13331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8649 eq13331
  have eq14969 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq14965
  have eq14970 : y = (M.op x x) ∨ x = y := by grind
  clear eq14969
  have eq15485 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1026 x X0
       have i₂ := eq14970
       grind)
    | exact superpose eq14970 eq1026
    | exact resolve eq1026 eq14970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15486 : ∀ X0 : G, y = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1181 X0 x
       have i₂ := eq14970
       grind)
    | exact superpose eq14970 eq1181
    | exact resolve eq1181 eq14970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14970
  have eq53972 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) = (M.op (M.op X0 X0) (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq169 (M.op X0 X0)
       have i₂ := eq362 X0 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))
       grind)
    | exact superpose eq362 eq169
    | (have j0 := eq169 (M.op X0 X0)
       have j1 := eq362 X0 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))
       grind)
    | exact resolve eq169 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq362
  have eq53977 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) = (M.op (M.op X0 X0) (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq53972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53972
  have eq53999 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq53977 X0
       have i₂ := eq1181 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq1181 eq53977
    | (have j0 := eq53977 X0
       grind)
    | exact resolve eq53977 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq53977
  have eq54000 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq53999 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53999
  have eq54512 : y = (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq54000 y
       have i₂ := eq15486 y
       grind)
    | exact superpose eq15486 eq54000
    | exact resolve eq54000 eq15486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15486
  have eq54566 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       have i₂ := eq54000 X0
       grind)
    | exact superpose eq54000 eq10
    | exact resolve eq10 eq54000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54000
  have eq55422 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op (σ y) (σ y))
       have i₂ := eq54512
       grind)
    | exact superpose eq54512 eq10
    | exact resolve eq10 eq54512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54512
  have eq56068 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1026 (σ y) X0
       have i₂ := eq55422
       grind)
    | exact superpose eq55422 eq1026
    | exact resolve eq1026 eq55422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55422
  have eq56813 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq56068 (σ x)
       grind)
    | exact superpose eq56068 eq14
    | exact resolve eq14 eq56068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56068
  have eq58621 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq56813
       have i₂ := eq15485 x
       grind)
    | exact superpose eq15485 eq56813
    | exact resolve eq56813 eq15485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15485 eq56813
  have eq58624 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq58621
  have eq58625 : x = y := by grind
  clear eq58624
  have eq59486 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58625
       grind)
    | exact superpose eq58625 eq14
    | exact resolve eq14 eq58625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58625
  have eq60090 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq59486
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq59486
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq59486
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq59486
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq59486 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72903 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1026 (σ (M.op X0 X0)) X1
       have i₂ := eq54566 X0
       grind)
    | exact superpose eq54566 eq1026
    | exact resolve eq1026 eq54566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54566
  have eq204073 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq60090 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60090
  have eq204074 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq204073
       have i₂ := eq72903 x (σ x)
       grind)
    | exact superpose eq72903 eq204073
    | exact resolve eq204073 eq72903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204073
  have eq204960 : (τ (σ x)) = (k (τ (σ x)) (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq38 (σ x) (M.op x x)
       have i₂ := eq204074
       grind)
    | exact superpose eq204074 eq38
    | (have j0 := eq38 (σ x) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq38 eq204074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq204074
  have eq204974 : x = (k x (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq204960
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq204960
    | exact resolve eq204960 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204960
  have eq204979 : x = (M.op x x) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq204974
  have eq204981 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq204979
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq204979
    | exact resolve eq204979 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204979
  have eq204982 : x = (M.op x x) := by grind
  clear eq204981
  have eq206025 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1026 x X0
       have i₂ := eq204982
       grind)
    | exact superpose eq204982 eq1026
    | exact resolve eq1026 eq204982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq206036 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq72903 x X0
       have i₂ := eq204982
       grind)
    | exact superpose eq204982 eq72903
    | exact resolve eq72903 eq204982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72903 eq204982
  have eq212592 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq59486
       have i₂ := eq206036 (σ x)
       grind)
    | exact superpose eq206036 eq59486
    | exact resolve eq59486 eq206036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59486 eq206036
  have eq212633 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq212592
       have i₂ := eq206025 x
       grind)
    | exact superpose eq206025 eq212592
    | exact resolve eq212592 eq206025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206025 eq212592
  have eq212634 : False := by grind
  exact eq212634

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation1043 : Law3.StructuralFromFin Law1043 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V1_Equation1043

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
