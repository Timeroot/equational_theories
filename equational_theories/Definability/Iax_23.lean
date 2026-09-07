import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4301 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq40 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq144 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq34 (τ X1) X0
       grind)
    | exact superpose eq34 eq17
    | (have j1 := eq34 (τ X1) X0
       grind)
    | exact resolve eq17 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq45
  have eq167 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq153 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq153
    | exact resolve eq153 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq443 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X2 X0)
       have i₂ := eq22 X0 X2 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 (M.op X0 X3)
       have i₂ := eq22 X3 X0 X1 X3
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq450 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq465 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq167 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq167
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq167 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X3 X0) ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq443 X1 X2 X3 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq443 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X2 X3)
       grind)
    | exact superpose eq12 eq443
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X4) (M.op X5 (M.op X2 X5))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq443 X2 x X0 X1
       grind)
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq443 X0 X1 X2 x
       grind)
    | exact superpose eq443 eq22
    | exact resolve eq22 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq443
  have eq984 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X4 X2 X2
       have i₂ := eq448 X2 X2 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1 X3 X2
       have i₂ := eq448 X0 X1 X2 X3
       grind)
    | exact superpose eq448 eq19
    | exact resolve eq19 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 x X1 X0
       have i₂ := eq448 X1 (M.op X1 x) X2 X3
       grind)
    | (have i₁ := eq19 X3 X1 (M.op X3 X1) X3
       have i₂ := eq448 X0 X1 (M.op X3 X1) X3
       grind)
    | exact superpose eq448 eq19
    | exact resolve eq19 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1715 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq37 x y
       grind)
    | exact superpose eq37 eq14
    | (have j1 := eq37 x y
       grind)
    | exact resolve eq14 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1748 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq9
    | (have j1 := eq37 X0 X1
       grind)
    | exact resolve eq9 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1789 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq16958 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1789 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1789
    | (have j0 := eq1789 (τ X0)
       grind)
    | exact resolve eq1789 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq16960 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16958 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16958
    | (have j0 := eq16958 X0
       grind)
    | exact resolve eq16958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16958
  have eq16963 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16960 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16960
    | (have j0 := eq16960 X0
       grind)
    | exact resolve eq16960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16960
  have eq17001 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq17181 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17001 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq17001
    | (have j0 := eq17001 X0 X1
       grind)
    | exact resolve eq17001 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17001
  have eq17202 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16963 (τ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq16963
    | (have j0 := eq16963 (τ X0)
       grind)
    | exact resolve eq16963 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq16963
  have eq17204 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144
    | exact resolve eq144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq17245 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17204 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq17204
    | (have j0 := eq17204 X0 X1
       grind)
    | exact resolve eq17204 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17204
  have eq90397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1715
       have i₂ := eq17245 y x
       grind)
    | exact superpose eq17245 eq1715
    | (have j1 := eq17245 y x
       grind)
    | (have r₁ := eq1715
       have r₂ := eq17245 y x
       grind)
    | exact resolve eq1715 eq17245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17245
  have eq90398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1715
       have i₂ := eq17181 y x
       grind)
    | exact superpose eq17181 eq1715
    | (have j1 := eq17181 (σ y) (σ x)
       grind)
    | (have r₁ := eq1715
       have r₂ := eq17181 y x
       grind)
    | exact resolve eq1715 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq90399 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq90398
  have eq90400 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq90397
  have eq90410 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq167
    | exact resolve eq167 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90598 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90410
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq90410
    | exact resolve eq90410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90410
  have eq90691 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq90598
       grind)
    | exact superpose eq90598 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq90598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90694 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17181 y x
       have i₂ := eq90598
       grind)
    | exact superpose eq90598 eq17181
    | (have j0 := eq17181 y x
       grind)
    | exact resolve eq17181 eq90598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90598
  have eq90695 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq90694
  have eq90696 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq90691
  have eq92426 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1 y x
       have i₂ := eq90696
       grind)
    | exact superpose eq90696 eq448
    | exact resolve eq448 eq90696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92448 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1 y x
       have i₂ := eq90696
       grind)
    | exact superpose eq90696 eq989
    | exact resolve eq989 eq90696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98198 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq90400
       grind)
    | exact superpose eq90400 eq167
    | exact resolve eq167 eq90400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90400
  have eq98392 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq98198
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq98198
    | exact resolve eq98198 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98198
  have eq98393 : x = (k x y) := by grind
  clear eq98392
  have eq98454 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1748 x x
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq1748
    | exact resolve eq1748 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq98721 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98454
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq98454
    | exact resolve eq98454 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98454
  have eq114612 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92426 (σ x) (σ x)
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq92426
    | exact resolve eq92426 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92426
  have eq115370 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq114612
  have eq135986 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115370
       grind)
    | exact superpose eq115370 eq14
    | exact resolve eq14 eq115370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115370
  have eq138927 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq135986
       have i₂ := eq90695
       grind)
    | exact superpose eq90695 eq135986
    | exact resolve eq135986 eq90695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90695 eq135986
  have eq138928 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq138927
  have eq182890 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq17202 (σ X0)
       have i₂ := eq465 (σ X0) X0
       grind)
    | exact superpose eq465 eq17202
    | (have j0 := eq17202 (σ X0)
       have j1 := eq465 (σ X0) X0
       grind)
    | exact resolve eq17202 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq182911 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq182890 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182890
    | (have j0 := eq182890 X0
       grind)
    | exact resolve eq182890 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182890
  have eq182919 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq182911 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182911
    | (have j0 := eq182911 X0
       grind)
    | exact resolve eq182911 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182911
  have eq182921 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq182919 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182919
    | (have j0 := eq182919 X0
       grind)
    | exact resolve eq182919 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182919
  have eq182923 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq182921 X0
       have j1 := eq147 X0 X0
       grind)
    | (have r₁ := eq182921 x
       have r₂ := eq147 x x
       grind)
    | exact resolve eq182921 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq182921
  have eq186041 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq182923 x
       have i₂ := eq90399
       grind)
    | exact superpose eq90399 eq182923
    | (have j0 := eq182923 x
       grind)
    | exact resolve eq182923 eq90399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90399 eq182923
  have eq186058 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq186041
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq186041
    | exact resolve eq186041 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186041
  have eq203636 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq98721
       grind)
    | exact superpose eq98721 eq9
    | exact resolve eq9 eq98721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98721
  have eq203685 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq203636
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq203636
    | exact resolve eq203636 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203636
  have eq207156 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34 x x
       have i₂ := eq203685
       grind)
    | exact superpose eq203685 eq34
    | exact resolve eq34 eq203685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq203685
  have eq207164 : y = (M.op x x) ∨ x = y := by grind
  clear eq207156
  have eq211012 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq450 x x
       have i₂ := eq207164
       grind)
    | exact superpose eq207164 eq450
    | exact resolve eq450 eq207164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207164
  have eq228339 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq211012
       have i₂ := eq90696
       grind)
    | exact superpose eq90696 eq211012
    | exact resolve eq211012 eq90696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90696 eq211012
  have eq228372 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq228339
       have r₂ := eq186058
       grind)
    | exact resolve eq228339 eq186058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186058 eq228339
  have eq231288 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1789 x
       have i₂ := eq228372
       grind)
    | exact superpose eq228372 eq1789
    | (have j0 := eq1789 x
       grind)
    | exact resolve eq1789 eq228372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq228372
  have eq231304 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq231288
  have eq249796 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92448 (σ x) (σ x)
       have i₂ := eq231304
       grind)
    | exact superpose eq231304 eq92448
    | exact resolve eq92448 eq231304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92448
  have eq249799 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq249796
  have eq430981 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq231304
       have i₂ := eq249799
       grind)
    | exact superpose eq249799 eq231304
    | exact resolve eq231304 eq249799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231304 eq249799
  have eq431411 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq430981
  have eq431424 : y = (M.op x x) := by
    first
    | (have r₁ := eq431411
       have r₂ := eq138928
       grind)
    | exact resolve eq431411 eq138928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138928 eq431411
  have eq435995 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq448
    | exact resolve eq448 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq435996 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq450 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq450
    | exact resolve eq450 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq436064 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq714 X0 X1 x X2 x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq714
    | exact resolve eq714 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq436092 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq984 X0 X1 X2 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq984
    | exact resolve eq984 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq436094 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1 x x
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq989
    | exact resolve eq989 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq436155 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq436092 x x X2
       have i₂ := eq436094 x x
       grind)
    | exact superpose eq436094 eq436092
    | exact resolve eq436092 eq436094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436092 eq436094
  have eq461861 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq17202 (M.op x y)
       have i₂ := eq435996
       grind)
    | exact superpose eq435996 eq17202
    | (have j0 := eq17202 (M.op x y)
       grind)
    | exact resolve eq17202 eq435996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17202 eq435996
  have eq461871 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq461861
  have eq636808 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq436064 (τ (M.op x y)) (τ (M.op x y)) X0
       have i₂ := eq461871
       grind)
    | exact superpose eq461871 eq436064
    | exact resolve eq436064 eq461871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436064
  have eq636827 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq636808 X0
       have i₂ := eq461871
       grind)
    | exact superpose eq461871 eq636808
    | exact resolve eq636808 eq461871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461871 eq636808
  have eq636972 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq636827 x
       have i₂ := eq436155 (M.op x x)
       grind)
    | exact superpose eq436155 eq636827
    | exact resolve eq636827 eq436155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636827
  have eq639292 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq636972
       grind)
    | exact superpose eq636972 eq10
    | exact resolve eq10 eq636972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661856 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq660 (σ y) X0 X1 (σ x)
       grind)
    | exact superpose eq660 eq14
    | (have j1 := eq660 (σ y) X1 x (σ x)
       grind)
    | exact resolve eq14 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq661917 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq661856 X0 X1
       have i₂ := eq639292
       grind)
    | exact superpose eq639292 eq661856
    | exact resolve eq661856 eq639292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661856
  have eq662018 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq661917 x x
       have r₂ := eq435995 x x
       grind)
    | exact resolve eq661917 eq435995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661917
  have eq662046 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq662018
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq662018
    | exact resolve eq662018 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662018
  have eq662052 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq662046
       have i₂ := eq98393
       grind)
    | exact superpose eq98393 eq662046
    | exact resolve eq662046 eq98393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98393 eq662046
  have eq662069 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq662052
       grind)
    | exact superpose eq662052 eq14
    | exact resolve eq14 eq662052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662436 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq435995 (σ x) (σ y)
       have i₂ := eq662052
       grind)
    | exact superpose eq662052 eq435995
    | exact resolve eq435995 eq662052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662659 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq662069
       have i₂ := eq639292
       grind)
    | exact superpose eq639292 eq662069
    | exact resolve eq662069 eq639292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662069
  have eq664950 : x = (k x (τ (M.op x y))) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq662436
       grind)
    | exact superpose eq662436 eq167
    | exact resolve eq167 eq662436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq662436
  have eq665451 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq664950
       have i₂ := eq636972
       grind)
    | exact superpose eq636972 eq664950
    | exact resolve eq664950 eq636972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636972 eq664950
  have eq666160 : (σ x) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17181 (M.op x y) x
       have i₂ := eq665451
       grind)
    | exact superpose eq665451 eq17181
    | (have j0 := eq17181 (M.op x y) x
       grind)
    | exact resolve eq17181 eq665451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17181 eq665451
  have eq666165 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq666160
       have i₂ := eq435995 x y
       grind)
    | exact superpose eq435995 eq666160
    | exact resolve eq666160 eq435995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435995 eq666160
  have eq666179 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq666165
       have i₂ := eq639292
       grind)
    | exact superpose eq639292 eq666165
    | exact resolve eq666165 eq639292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666165
  have eq666187 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq666179
       have r₂ := eq662659
       grind)
    | exact resolve eq666179 eq662659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666179
  have eq666189 : y = (M.op x y) := by
    first
    | (have i₁ := eq666187
       have i₂ := eq431424
       grind)
    | exact superpose eq431424 eq666187
    | exact resolve eq666187 eq431424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431424 eq666187
  have eq666929 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq436155 x
       have i₂ := eq666189
       grind)
    | exact superpose eq666189 eq436155
    | exact resolve eq436155 eq666189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436155
  have eq666943 : y = (σ y) := by
    first
    | (have i₁ := eq639292
       have i₂ := eq666189
       grind)
    | exact superpose eq666189 eq639292
    | exact resolve eq639292 eq666189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639292
  have eq666948 : y ≠ (σ x) := by
    first
    | (have i₁ := eq662659
       have i₂ := eq666189
       grind)
    | exact superpose eq666189 eq662659
    | exact resolve eq662659 eq666189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662659 eq666189
  have eq670340 : (σ x) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq662052
       have i₂ := eq666943
       grind)
    | exact superpose eq666943 eq662052
    | exact resolve eq662052 eq666943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662052 eq666943
  have eq670433 : y = (σ x) := by
    first
    | (have i₁ := eq670340
       have i₂ := eq666929 (σ x)
       grind)
    | exact superpose eq666929 eq670340
    | exact resolve eq670340 eq666929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666929 eq670340
  have eq670457 : False := by grind
  exact eq670457

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4301 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4301 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 X0 X0 x
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 (M.op X1 X3)
       have i₂ := eq8 X1 X3 X0
       grind)
    | (have i₁ := eq8 X2 X1 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X1 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq29
  have eq84 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq131 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq44
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq32
    | exact resolve eq32 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 (M.op X3 X0)) ∨ (M.op X3 X0) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X3 X3 X2 X1
       have i₂ := eq12 X0 X3
       grind)
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 X3
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X2 X0)
       have i₂ := eq22 X0 X2 X3 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 (M.op X0 X3)
       have i₂ := eq22 X3 X0 X1 X3
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq452 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq717 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X4) (M.op X5 (M.op X2 X5))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq445 X2 x X0 X1
       grind)
    | (have i₁ := eq22 X5 X2 x X4
       have i₂ := eq445 X0 X1 X2 x
       grind)
    | exact superpose eq445 eq22
    | exact resolve eq22 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq987 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X4 X2 X2
       have i₂ := eq450 X2 X2 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1 X3 X2
       have i₂ := eq450 X0 X1 X2 X3
       grind)
    | exact superpose eq450 eq19
    | exact resolve eq19 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 x X1 X0
       have i₂ := eq450 X1 (M.op X1 x) X2 X3
       grind)
    | (have i₁ := eq19 X3 X1 (M.op X3 X1) X3
       have i₂ := eq450 X0 X1 (M.op X3 X1) X3
       grind)
    | exact superpose eq450 eq19
    | exact resolve eq19 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1718 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1792 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq16963 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1792 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1792
    | (have j0 := eq1792 (τ X0)
       grind)
    | exact resolve eq1792 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq16965 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16963 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16963
    | (have j0 := eq16963 X0
       grind)
    | exact resolve eq16963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16963
  have eq16968 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16965 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16965
    | (have j0 := eq16965 X0
       grind)
    | exact resolve eq16965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16965
  have eq17006 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17158 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq10
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq17186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17006 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq17006
    | (have j0 := eq17006 X0 X1
       grind)
    | exact resolve eq17006 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17006
  have eq17207 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16968 (τ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq16968
    | (have j0 := eq16968 (τ X0)
       grind)
    | exact resolve eq16968 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq16968
  have eq18117 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq445 X2 X3 (σ X1) (σ X0)
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq445
    | (have j1 := eq140 X0 X1
       grind)
    | exact resolve eq445 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq445
  have eq85736 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X1 X1
       have i₂ := eq34 (M.op X1 X1) X1 x
       grind)
    | (have i₁ := eq452 X1 X1
       have i₂ := eq34 X0 X1 X1
       grind)
    | exact superpose eq34 eq452
    | (have j1 := eq34 X1 X0 x
       grind)
    | exact resolve eq452 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq90383 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1718
       have i₂ := eq17186 y x
       grind)
    | exact superpose eq17186 eq1718
    | (have j1 := eq17186 (σ y) (σ x)
       grind)
    | (have r₁ := eq1718
       have r₂ := eq17186 y x
       grind)
    | exact resolve eq1718 eq17186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq90384 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq90383
  have eq90395 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq84
    | exact resolve eq84 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90581 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90395
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq90395
    | exact resolve eq90395 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90395
  have eq90670 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq90581
       grind)
    | exact superpose eq90581 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq90581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90673 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17186 y x
       have i₂ := eq90581
       grind)
    | exact superpose eq90581 eq17186
    | (have j0 := eq17186 y x
       grind)
    | exact resolve eq17186 eq90581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17186 eq90581
  have eq90674 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq90673
  have eq90675 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq90670
  have eq92410 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1 y x
       have i₂ := eq90675
       grind)
    | exact superpose eq90675 eq450
    | exact resolve eq450 eq90675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92432 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1 y x
       have i₂ := eq90675
       grind)
    | exact superpose eq90675 eq992
    | exact resolve eq992 eq90675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90675
  have eq98447 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1751 x x
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq1751
    | exact resolve eq1751 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq98714 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98447
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq98447
    | exact resolve eq98447 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98447
  have eq112079 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92410 (σ x) (σ x)
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq92410
    | exact resolve eq92410 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92410
  have eq112829 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq112079
  have eq132947 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq112829
       grind)
    | exact superpose eq112829 eq14
    | exact resolve eq14 eq112829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112829
  have eq136098 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132947
       have i₂ := eq90674
       grind)
    | exact superpose eq90674 eq132947
    | exact resolve eq132947 eq90674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90674 eq132947
  have eq136099 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq136098
  have eq186494 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq98714
       grind)
    | exact superpose eq98714 eq9
    | exact resolve eq9 eq98714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98714
  have eq186542 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq186494
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq186494
    | exact resolve eq186494 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186494
  have eq189894 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32 x x
       have i₂ := eq186542
       grind)
    | exact superpose eq186542 eq32
    | exact resolve eq32 eq186542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq186542
  have eq189902 : y = (M.op x x) ∨ x = y := by grind
  clear eq189894
  have eq306176 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1
       have i₂ := eq131 (σ X1) X0
       grind)
    | exact superpose eq131 eq84
    | (have j1 := eq131 (σ X1) X0
       grind)
    | exact resolve eq84 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq131
  have eq306199 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306176 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq306176
    | (have j0 := eq306176 X0 X1
       grind)
    | exact resolve eq306176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306176
  have eq306249 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq306199 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq306199
    | (have j0 := eq306199 X0 X1
       grind)
    | exact resolve eq306199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306199
  have eq324055 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq306249 x x
       have i₂ := eq90384
       grind)
    | exact superpose eq90384 eq306249
    | (have j0 := eq306249 x x
       grind)
    | exact resolve eq306249 eq90384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90384 eq306249
  have eq324126 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq324055
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq324055
    | exact resolve eq324055 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324055
  have eq371886 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq324126
  have eq371906 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq371886
       have r₂ := eq189902
       grind)
    | exact resolve eq371886 eq189902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189902 eq371886
  have eq386520 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1792 x
       have i₂ := eq371906
       grind)
    | exact superpose eq371906 eq1792
    | (have j0 := eq1792 x
       grind)
    | exact resolve eq1792 eq371906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371906
  have eq386543 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq386520
  have eq400050 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92432 (σ x) (σ x)
       have i₂ := eq386543
       grind)
    | exact superpose eq386543 eq92432
    | exact resolve eq92432 eq386543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92432
  have eq400065 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq400050
  have eq496320 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq386543
       have i₂ := eq400065
       grind)
    | exact superpose eq400065 eq386543
    | exact resolve eq386543 eq400065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386543 eq400065
  have eq496503 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq496320
  have eq496512 : y = (M.op x x) := by
    first
    | (have r₁ := eq496503
       have r₂ := eq136099
       grind)
    | exact resolve eq496503 eq136099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136099 eq496503
  have eq500906 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq269 x X1 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq269
    | exact resolve eq269 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq501019 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq450
    | exact resolve eq450 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq501020 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq452 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq452
    | exact resolve eq452 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq501098 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq717 X0 X1 x X2 x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq717
    | exact resolve eq717 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq501129 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq987 X0 X1 X2 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq987
    | exact resolve eq987 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq501131 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq992
    | exact resolve eq992 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq501206 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq501129 x x X2
       have i₂ := eq501131 x x
       grind)
    | exact superpose eq501131 eq501129
    | exact resolve eq501129 eq501131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501129
  have eq501233 : ∀ X1 : G, (M.op x y) = (M.op X1 y) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq500906 x X1
       have i₂ := eq501131 x X1
       grind)
    | exact superpose eq501131 eq500906
    | exact resolve eq500906 eq501131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500906 eq501131
  have eq530154 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq17207 (M.op x y)
       have i₂ := eq501020
       grind)
    | exact superpose eq501020 eq17207
    | (have j0 := eq17207 (M.op x y)
       grind)
    | exact resolve eq17207 eq501020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17207 eq501020
  have eq530169 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq530154
  have eq551698 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq501233 X1
       have i₂ := eq501233 X0
       grind)
    | (have i₁ := eq501233 X1
       have i₂ := eq501233 x
       grind)
    | exact superpose eq501233 eq501233
    | exact resolve eq501233 eq501233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551734 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (M.op X0 y)) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq501206 x
       have i₂ := eq501233 X1
       grind)
    | (have i₁ := eq501206 x
       have i₂ := eq501233 x
       grind)
    | exact superpose eq501233 eq501206
    | exact resolve eq501206 eq501233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501233
  have eq552387 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have j0 := eq551698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551698
  have eq656929 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq501098 (τ (M.op x y)) (τ (M.op x y)) X0
       have i₂ := eq530169
       grind)
    | exact superpose eq530169 eq501098
    | exact resolve eq501098 eq530169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501098
  have eq656948 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq656929 X0
       have i₂ := eq530169
       grind)
    | exact superpose eq530169 eq656929
    | exact resolve eq656929 eq530169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530169 eq656929
  have eq657087 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq656948 x
       have i₂ := eq501206 (M.op x x)
       grind)
    | exact superpose eq501206 eq656948
    | exact resolve eq656948 eq501206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501206 eq656948
  have eq658166 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq657087
       grind)
    | exact superpose eq657087 eq10
    | exact resolve eq10 eq657087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657087
  have eq659084 : ∀ X0 : G, (M.op X0 y) = (σ (M.op X0 y)) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq658166
       have i₂ := eq552387 x x
       grind)
    | (have i₁ := eq658166
       have i₂ := eq552387 X0 x
       grind)
    | exact superpose eq552387 eq658166
    | exact resolve eq658166 eq552387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665821 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq17158 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17158
  have eq665822 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq665821 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq665821
    | (have j0 := eq665821 X0
       grind)
    | exact resolve eq665821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665821
  have eq665897 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq665822 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq665822
    | (have j0 := eq665822 (σ X0)
       grind)
    | exact resolve eq665822 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665822
  have eq665912 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq665897 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq665897
    | (have j0 := eq665897 X0
       grind)
    | exact resolve eq665897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665897
  have eq786922 : y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq85736 x x
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq85736
    | exact resolve eq85736 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85736
  have eq786970 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq665912 y
       have i₂ := eq786922
       grind)
    | exact superpose eq786922 eq665912
    | (have j0 := eq665912 y
       grind)
    | exact resolve eq665912 eq786922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665912 eq786922
  have eq786982 : (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by grind
  clear eq786970
  have eq787171 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq786982
       have i₂ := eq552387 y X0
       grind)
    | (have i₁ := eq786982
       have i₂ := eq552387 X0 y
       grind)
    | exact superpose eq552387 eq786982
    | exact resolve eq786982 eq552387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552387 eq786982
  have eq787210 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq787171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787171
  have eq787568 : ∀ X0 : G, (σ y) = (M.op X0 y) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq659084 X0
       have i₂ := eq787210 X0
       grind)
    | exact superpose eq787210 eq659084
    | exact resolve eq659084 eq787210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659084
  have eq787600 : ∀ X0 : G, (σ y) = (M.op X0 y) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq787568 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787568
  have eq795801 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ y = (k x x) ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq551734 x X1
       have i₂ := eq787600 x
       grind)
    | exact superpose eq787600 eq551734
    | exact resolve eq551734 eq787600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551734 eq787600
  have eq796246 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ y = (k x x) := by
    intro X1
    first
    | (have j0 := eq795801 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795801
  have eq802147 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq796246 (σ x)
       grind)
    | exact superpose eq796246 eq14
    | exact resolve eq14 eq796246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796246
  have eq802160 : y = (k x x) := by
    first
    | (have r₁ := eq802147
       have r₂ := eq787210 x
       grind)
    | exact resolve eq802147 eq787210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787210 eq802147
  have eq804705 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1792 x
       have i₂ := eq802160
       grind)
    | exact superpose eq802160 eq1792
    | (have j0 := eq1792 x
       grind)
    | exact resolve eq1792 eq802160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq974653 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq18117 x x x x
       have i₂ := eq802160
       grind)
    | exact superpose eq802160 eq18117
    | exact resolve eq18117 eq802160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18117 eq802160
  have eq974764 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq974653 x x
       have i₂ := eq501019 x x
       grind)
    | exact superpose eq501019 eq974653
    | exact resolve eq974653 eq501019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501019 eq974653
  have eq974783 : (M.op x y) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq974764
       grind)
    | exact superpose eq974764 eq14
    | exact resolve eq14 eq974764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974764
  have eq974973 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq974783
       have r₂ := eq658166
       grind)
    | exact resolve eq974783 eq658166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974783
  have eq975172 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq974973
       grind)
    | exact superpose eq974973 eq14
    | exact resolve eq14 eq974973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975193 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq804705
       have i₂ := eq974973
       grind)
    | exact superpose eq974973 eq804705
    | (have r₁ := eq804705
       have r₂ := eq974973
       grind)
    | exact resolve eq804705 eq974973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804705
  have eq975194 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq974973
       grind)
    | exact superpose eq974973 eq9
    | exact resolve eq9 eq974973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974973
  have eq975250 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq975193
  have eq975274 : x = y := by
    first
    | (have i₁ := eq975194
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq975194
    | exact resolve eq975194 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975194
  have eq975275 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq975172
       have i₂ := eq975250
       grind)
    | exact superpose eq975250 eq975172
    | exact resolve eq975172 eq975250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975172 eq975250
  have eq975277 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq975275
       have i₂ := eq658166
       grind)
    | exact superpose eq658166 eq975275
    | exact resolve eq975275 eq658166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975275
  have eq975279 : (σ x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq975277
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq975277
    | exact resolve eq975277 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975277
  have eq975281 : y ≠ (σ x) := by
    first
    | (have i₁ := eq975279
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq975279
    | exact resolve eq975279 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975279
  have eq975283 : x ≠ (σ x) := by
    first
    | (have i₁ := eq975281
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq975281
    | exact resolve eq975281 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975281
  have eq975603 : (M.op x x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq658166
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq658166
    | exact resolve eq658166 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658166
  have eq975723 : y = (σ y) := by
    first
    | (have i₁ := eq975603
       have i₂ := eq496512
       grind)
    | exact superpose eq496512 eq975603
    | exact resolve eq975603 eq496512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496512 eq975603
  have eq975783 : x = (σ x) := by
    first
    | (have i₁ := eq975723
       have i₂ := eq975274
       grind)
    | exact superpose eq975274 eq975723
    | exact resolve eq975723 eq975274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975274 eq975723
  have eq975825 : False := by grind
  exact eq975825

/-- `Equation4315`: `x ◇ (y ◇ x) = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4315 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4315 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4315.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X2 X1 X2
       have i₂ := eq8 X2 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27
    | exact resolve eq27 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq152 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 (M.op X1 X3)
       have i₂ := eq20 X0 X1 X3 X2
       grind)
    | (have i₁ := eq91 X0 (M.op X1 X3)
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq91
    | (have j0 := eq91 X0 (M.op X1 X3)
       grind)
    | (have r₁ := eq91 X0 (M.op X0 (M.op X0 X3))
       have r₂ := eq20 X0 X0 (M.op X0 X3) X3
       grind)
    | (have r₁ := eq91 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq20 X0 X0 X2 (M.op X0 X2)
       grind)
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq305 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op (σ X0) X3)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (σ X0) X3 (σ X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq20
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq33 X0 X2
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 X0 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq560 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq617 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1330 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq305
       have i₂ := eq617 y x
       grind)
    | exact superpose eq617 eq305
    | (have j1 := eq617 (σ y) (σ x)
       grind)
    | (have r₁ := eq305
       have r₂ := eq617 y x
       grind)
    | exact resolve eq305 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1331 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1330
  have eq1374 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (M.op (σ X1) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317 X1 X2
       have i₂ := eq317 X1 X0
       grind)
    | (have i₁ := eq317 X0 X1
       have i₂ := eq317 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq317 eq317
    | (have j0 := eq317 X1 X2
       have j1 := eq317 X1 X2
       grind)
    | exact resolve eq317 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq317 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq317
    | exact resolve eq317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op (σ X0) X3)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (σ X0) X3 (σ X1)
       have i₂ := eq317 X0 X1
       grind)
    | exact superpose eq317 eq20
    | (have j1 := eq317 X0 X1
       grind)
    | exact resolve eq20 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1431 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1381 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1381
    | (have j0 := eq1381 X0 X1
       grind)
    | exact resolve eq1381 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1381
  have eq3587 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (τ X0)) X3)) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq311 (τ X0) (τ X1) X2 X3
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq311
    | (have j0 := eq311 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq311 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq3916 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (τ X0)) X3)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3587 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3587
    | (have j0 := eq3587 X0 X1 X2 X3
       grind)
    | exact resolve eq3587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq3918 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3916 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3916
    | (have j0 := eq3916 X0 X1 X2 X3
       grind)
    | exact resolve eq3916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq3919 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3918 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3918
    | (have j0 := eq3918 X0 X1 X2 X3
       grind)
    | exact resolve eq3918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918
  have eq3920 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X1 ∨ (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3919 X0 X1 X2 X3
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3919
    | (have j0 := eq3919 X0 X1 X2 X3
       grind)
    | exact resolve eq3919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq5595 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1431 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1431
    | (have j0 := eq1431 X1 (τ X0)
       grind)
    | exact resolve eq1431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq10596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq319
  have eq32561 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X0 x (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq49968 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10596 (τ X1) (τ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq10596
    | exact resolve eq10596 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq49990 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10596 x x
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq10596
    | exact resolve eq10596 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq50029 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq10596 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10596
  have eq50030 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq50029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50029
  have eq50035 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq49990
  have eq50067 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49968 X0 X1
       have i₂ := eq50030 (τ X0)
       grind)
    | exact superpose eq50030 eq49968
    | (have j0 := eq49968 X0 X1
       grind)
    | exact resolve eq49968 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49968
  have eq50084 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50067 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq50067
    | (have j0 := eq50067 X0 X1
       grind)
    | exact resolve eq50067 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50067
  have eq50091 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50084 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50084
    | (have j0 := eq50084 X0 X1
       grind)
    | exact resolve eq50084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50084
  have eq50094 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50091 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq50091
    | (have j0 := eq50091 X0 X1
       grind)
    | exact resolve eq50091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50091
  have eq50096 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50094 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq50094
    | (have j0 := eq50094 X0 X1
       grind)
    | exact resolve eq50094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50094
  have eq50097 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50096 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50096
    | (have j0 := eq50096 X0 X1
       grind)
    | exact resolve eq50096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50096
  have eq50098 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50097 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq50097
    | (have j0 := eq50097 X0 X1
       grind)
    | exact resolve eq50097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50097
  have eq50123 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50030 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50030
    | exact resolve eq50030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50217 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5595 X1 (σ X0)
       have i₂ := eq50030 X0
       grind)
    | exact superpose eq50030 eq5595
    | (have j0 := eq5595 X1 (σ X0)
       grind)
    | exact resolve eq5595 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq50230 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op X1 (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (σ X0) X2 (σ X0)
       have i₂ := eq50030 X0
       grind)
    | exact superpose eq50030 eq20
    | exact resolve eq20 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50280 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50217 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq50217
    | (have j0 := eq50217 X0 X1
       grind)
    | exact resolve eq50217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50217
  have eq50310 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq50123 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq50123
    | exact resolve eq50123 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq50123
  have eq50323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq50310 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50310
    | exact resolve eq50310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50310
  have eq51544 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq50035
       grind)
    | exact superpose eq50035 eq9
    | exact resolve eq9 eq50035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50035
  have eq51636 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51544
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq51544
    | exact resolve eq51544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51544
  have eq51672 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51636
       have i₂ := eq50323 x
       grind)
    | exact superpose eq50323 eq51636
    | exact resolve eq51636 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51636
  have eq51673 : y = (M.op x x) := by grind
  clear eq51672
  have eq51711 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 x X1 x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq20
    | exact resolve eq20 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq51755 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq32561 x x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq32561
    | exact resolve eq32561 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51998 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (k x X2)) ∨ (M.op x x) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq3920 x X2 X0 x
       have i₂ := eq51711 X0 x
       grind)
    | exact superpose eq51711 eq3920
    | (have j0 := eq3920 x X2 X2 x
       grind)
    | exact resolve eq3920 eq51711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920 eq51711
  have eq52123 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (k x X2)) ∨ y = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq51998 X0 X2
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq51998
    | (have j0 := eq51998 X0 X2
       grind)
    | exact resolve eq51998 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51998
  have eq53161 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50230 X0 X1 X2
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq50230
    | exact resolve eq50230 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50230
  have eq53894 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53161 x X0 X1
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq53161
    | exact resolve eq53161 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53161
  have eq54334 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32561 (σ x) x
       have i₂ := eq53894 (σ x) x
       grind)
    | exact superpose eq53894 eq32561
    | exact resolve eq32561 eq53894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32561
  have eq55014 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1419 x (M.op x y) X0 X1
       have i₂ := eq51755
       grind)
    | exact superpose eq51755 eq1419
    | (have j0 := eq1419 x (M.op x y) x x
       grind)
    | exact resolve eq1419 eq51755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq55116 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq55014 X0 x
       have i₂ := eq53894 X0 x
       grind)
    | exact superpose eq53894 eq55014
    | exact resolve eq55014 eq53894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53894 eq55014
  have eq55128 : ∀ X0 : G, (M.op x y) = (τ (σ (k x x))) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55116 X0
       have i₂ := eq50030 x
       grind)
    | exact superpose eq50030 eq55116
    | (have j0 := eq55116 X0
       grind)
    | exact resolve eq55116 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50030 eq55116
  have eq55138 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55128 X0
       have i₂ := eq9 (k x x)
       grind)
    | exact superpose eq9 eq55128
    | (have j0 := eq55128 X0
       grind)
    | exact resolve eq55128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55128
  have eq55144 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55138 X0
       have i₂ := eq50323 x
       grind)
    | exact superpose eq50323 eq55138
    | (have j0 := eq55138 X0
       grind)
    | exact resolve eq55138 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55138
  have eq55146 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55144 X0
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq55144
    | (have j0 := eq55144 X0
       grind)
    | exact resolve eq55144 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55144
  have eq55901 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50098 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50098
  have eq55904 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55901 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq55901
    | (have j0 := eq55901 X0 X1
       grind)
    | (have r₁ := eq55901 X0 X0
       have r₂ := eq50323 X0
       grind)
    | exact resolve eq55901 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55901
  have eq55993 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55904 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq55904
    | (have j0 := eq55904 X0 X1
       grind)
    | exact resolve eq55904 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55904
  have eq56345 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq55993 x x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq55993
    | exact resolve eq55993 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51673 eq55993
  have eq56564 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq56345 (k x X0)
       have i₂ := eq52123 x X0
       grind)
    | exact superpose eq52123 eq56345
    | (have j0 := eq56345 y
       have j1 := eq52123 X0 (k x (k x X0))
       grind)
    | (have r₁ := eq56345 X0
       have r₂ := eq52123 X0 (M.op x X0)
       grind)
    | exact resolve eq56345 eq52123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52123 eq56345
  have eq58613 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq41 x (M.op (σ x) (σ y))
       have i₂ := eq54334
       grind)
    | exact superpose eq54334 eq41
    | exact resolve eq41 eq54334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq54334
  have eq60805 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq50280 X0 (σ X1)
       grind)
    | exact superpose eq50280 eq9
    | (have j1 := eq50280 X0 (σ X1)
       grind)
    | exact resolve eq9 eq50280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50280
  have eq60908 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60805 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq60805
    | (have j0 := eq60805 X0 X1
       grind)
    | exact resolve eq60805 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50323 eq60805
  have eq60950 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60908 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq60908
    | (have j0 := eq60908 X0 X1
       grind)
    | exact resolve eq60908 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60908
  have eq62499 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq617 X2 X1
       have i₂ := eq60950 X1 X0
       grind)
    | (have i₁ := eq617 X0 X1
       have i₂ := eq60950 X0 (M.op X1 X1)
       grind)
    | exact superpose eq60950 eq617
    | (have j0 := eq617 X2 X1
       have j1 := eq60950 X1 X0
       grind)
    | exact resolve eq617 eq60950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq60950
  have eq62854 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq1374 y x X0
       grind)
    | exact superpose eq1374 eq14
    | (have j1 := eq1374 y x X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq1374 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq1374 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq62858 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq62854 X0
       have j1 := eq62499 (σ (k x X0)) x (M.op (σ x) (σ X0))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 (σ (M.op x y)) x (σ (k x y))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 (σ (k x y)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 X0 x y
       grind)
    | exact resolve eq62854 eq62499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62499 eq62854
  have eq72325 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62858 (M.op x y)
       have i₂ := eq55146 (σ x)
       grind)
    | exact superpose eq55146 eq62858
    | (have j0 := eq62858 (M.op x y)
       grind)
    | exact resolve eq62858 eq55146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55146 eq62858
  have eq72361 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq72325
  have eq72365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72361
       have i₂ := eq51755
       grind)
    | exact superpose eq51755 eq72361
    | exact resolve eq72361 eq51755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51755 eq72361
  have eq72370 : y = (M.op x y) := by
    first
    | (have r₁ := eq72365
       have r₂ := eq14
       grind)
    | exact resolve eq72365 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72365
  have eq72389 : ∀ X0 : G, y ≠ y ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq56564 X0
       have i₂ := eq72370
       grind)
    | exact superpose eq72370 eq56564
    | (have j0 := eq56564 X0
       grind)
    | (have r₁ := eq56564 X0
       have r₂ := eq72370
       grind)
    | exact resolve eq56564 eq72370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56564
  have eq72505 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq72389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72389
  have eq73386 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72505 (τ (M.op (σ x) (σ y)))
       have i₂ := eq58613
       grind)
    | exact superpose eq58613 eq72505
    | (have j0 := eq72505 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq72505 eq58613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72505
  have eq73658 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq73386
       have i₂ := eq58613
       grind)
    | exact superpose eq58613 eq73386
    | exact resolve eq73386 eq58613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58613 eq73386
  have eq73659 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq73658
  have eq73822 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq73659
       grind)
    | exact superpose eq73659 eq10
    | exact resolve eq10 eq73659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73659
  have eq74390 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq73822
       grind)
    | exact superpose eq73822 eq14
    | exact resolve eq14 eq73822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73822
  have eq74601 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq74390
       have i₂ := eq72370
       grind)
    | exact superpose eq72370 eq74390
    | exact resolve eq74390 eq72370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72370 eq74390
  have eq74602 : False := by grind
  exact eq74602

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation432 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law432 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq39 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq26 (τ X0) X1
       grind)
    | exact superpose eq26 eq17
    | (have j1 := eq26 (τ X0) X1
       grind)
    | exact resolve eq17 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq26 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq97 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq99 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq44
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq111 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (M.op X0 X1)
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq62
    | (have j0 := eq62 X1 X0
       grind)
    | exact resolve eq62 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq111
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq111 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq111
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq605 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq681 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq706 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59
    | exact resolve eq59 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq749 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq706
    | (have j0 := eq706 X0 X1
       grind)
    | exact resolve eq706 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq1014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq19
    | (have j1 := eq56 X0 X1
       grind)
    | exact resolve eq19 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1499 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181 x y
       grind)
    | exact superpose eq181 eq14
    | (have j1 := eq181 x y
       grind)
    | exact resolve eq14 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1515 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2080 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq166 (τ X1) (τ X0)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq166
    | (have j0 := eq166 (τ X0) (τ X1)
       grind)
    | exact resolve eq166 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq166
  have eq2129 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2080 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2080
    | (have j0 := eq2080 X0 X1
       grind)
    | exact resolve eq2080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq2133 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2129 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2129
    | (have j0 := eq2129 X0 X1
       grind)
    | exact resolve eq2129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq2134 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2135 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2134 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2134
    | (have j0 := eq2134 X0 X1
       grind)
    | exact resolve eq2134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq10389 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq255 x y
       grind)
    | exact superpose eq255 eq14
    | (have j1 := eq255 x y
       grind)
    | exact resolve eq14 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq10424 : y = (k y x) := by
    first
    | (have j1 := eq749 x y
       grind)
    | (have r₁ := eq10389
       have r₂ := eq749 x y
       grind)
    | exact resolve eq10389 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq10389
  have eq10961 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq681 x y
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq681
    | (have j0 := eq681 x y
       grind)
    | exact resolve eq681 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10963 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1515 x y
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq1515
    | (have j0 := eq1515 x y
       grind)
    | exact resolve eq1515 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10964 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2135 y x
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq2135
    | (have j0 := eq2135 y y
       grind)
    | exact resolve eq2135 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq12030 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq140 y y
       have i₂ := eq10964
       grind)
    | exact superpose eq10964 eq140
    | (have r₁ := eq140 y y
       have r₂ := eq10964
       grind)
    | exact resolve eq140 eq10964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq12034 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq10964
  have eq12035 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq12030
  have eq13347 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1515 y y
       have i₂ := eq12035
       grind)
    | exact superpose eq12035 eq1515
    | (have j0 := eq1515 y y
       grind)
    | exact resolve eq1515 eq12035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515 eq12035
  have eq13352 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq13347
  have eq21632 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq681 x y
       grind)
    | exact superpose eq681 eq1499
    | (have j1 := eq681 x y
       grind)
    | (have r₁ := eq1499
       have r₂ := eq681 x y
       grind)
    | exact resolve eq1499 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq1499
  have eq21641 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq21632
  have eq21899 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21641
       grind)
    | exact superpose eq21641 eq14
    | exact resolve eq14 eq21641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21911 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99 (σ x) y
       have i₂ := eq21641
       grind)
    | exact superpose eq21641 eq99
    | (have j0 := eq99 (σ x) y
       grind)
    | exact resolve eq99 eq21641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq21641
  have eq21956 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21911
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq21911
    | exact resolve eq21911 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21911
  have eq21978 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21956
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq21956
    | exact resolve eq21956 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10424 eq21956
  have eq21983 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq21978
       have r₂ := eq12034
       grind)
    | exact resolve eq21978 eq12034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034 eq21978
  have eq22327 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21899
       have i₂ := eq10961
       grind)
    | exact superpose eq10961 eq21899
    | exact resolve eq21899 eq10961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10961 eq21899
  have eq22329 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq22327
  have eq24031 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13352
       have i₂ := eq21983
       grind)
    | exact superpose eq21983 eq13352
    | exact resolve eq13352 eq21983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13352 eq21983
  have eq24103 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq24031
  have eq24134 : x = (M.op y y) := by
    first
    | (have r₁ := eq24103
       have r₂ := eq22329
       grind)
    | exact resolve eq24103 eq22329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22329 eq24103
  have eq24595 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq8
    | exact resolve eq8 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24597 : x = (M.op x y) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq19
    | exact resolve eq19 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq24598 : ∀ X0 : G, y = (M.op y (M.op X0 x)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq28 y y x
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq28
    | exact resolve eq28 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq29726 : y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq24595 y
       have i₂ := eq24598 y
       grind)
    | exact superpose eq24598 eq24595
    | exact resolve eq24595 eq24598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24595 eq24598
  have eq29762 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq29726
       have i₂ := eq24134
       grind)
    | exact superpose eq24134 eq29726
    | exact resolve eq29726 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24134 eq29726
  have eq30441 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1014 y y
       have i₂ := eq29762
       grind)
    | exact superpose eq29762 eq1014
    | exact resolve eq1014 eq29762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq29762
  have eq30461 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq30441
       have r₂ := eq10963
       grind)
    | exact resolve eq30441 eq10963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30441
  have eq30983 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq30461
       grind)
    | exact superpose eq30461 eq14
    | exact resolve eq14 eq30461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30461
  have eq31050 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq30983
       have i₂ := eq24597
       grind)
    | exact superpose eq24597 eq30983
    | exact resolve eq30983 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30983
  have eq31051 : x = y := by grind
  clear eq31050
  have eq31680 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31051
       grind)
    | exact superpose eq31051 eq14
    | exact resolve eq14 eq31051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31688 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10963
       have i₂ := eq31051
       grind)
    | exact superpose eq31051 eq10963
    | exact resolve eq10963 eq31051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10963
  have eq31726 : x = (M.op x x) := by
    first
    | (have i₁ := eq24597
       have i₂ := eq31051
       grind)
    | exact superpose eq31051 eq24597
    | exact resolve eq24597 eq31051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24597 eq31051
  have eq31740 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31688
  have eq31746 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31680
       have i₂ := eq31726
       grind)
    | exact superpose eq31726 eq31680
    | exact resolve eq31680 eq31726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31680 eq31726
  have eq31747 : False := by grind
  exact eq31747

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation432 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law432 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X2 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35
    | exact resolve eq35 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq35
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq26 (τ X0) X1
       grind)
    | exact superpose eq26 eq16
    | (have j1 := eq26 (τ X0) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq57
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq57 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57
  have eq255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq605 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq681 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq706 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
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
  have eq749 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq706
    | (have j0 := eq706 X0 X1
       grind)
    | exact resolve eq706 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq1014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq19
    | (have j1 := eq58 X0 X1
       grind)
    | exact resolve eq19 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1500 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181 x y
       grind)
    | exact superpose eq181 eq14
    | (have j1 := eq181 x y
       grind)
    | exact resolve eq14 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1516 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2118 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq166 (τ X1) (τ X0)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq166
    | (have j0 := eq166 (τ X0) (τ X1)
       grind)
    | exact resolve eq166 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq166
  have eq2175 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2118 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2118
    | (have j0 := eq2118 X0 X1
       grind)
    | exact resolve eq2118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2177 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2175 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2175
    | (have j0 := eq2175 X0 X1
       grind)
    | exact resolve eq2175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2178 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2177 X0 X0
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
  have eq2179 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2178 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2178
    | (have j0 := eq2178 X0 X1
       grind)
    | exact resolve eq2178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq8966 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq255 x y
       grind)
    | exact superpose eq255 eq14
    | (have j1 := eq255 x y
       grind)
    | exact resolve eq14 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq8999 : y = (k x y) := by
    first
    | (have j1 := eq749 x y
       grind)
    | (have r₁ := eq8966
       have r₂ := eq749 x y
       grind)
    | exact resolve eq8966 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq8966
  have eq9612 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq681 x y
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq681
    | (have j0 := eq681 x y
       grind)
    | exact resolve eq681 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9614 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1516 x y
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq1516
    | (have j0 := eq1516 x y
       grind)
    | exact resolve eq1516 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9615 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2179 x y
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq2179
    | (have j0 := eq2179 y y
       grind)
    | exact resolve eq2179 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq11150 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq140 y y
       have i₂ := eq9615
       grind)
    | exact superpose eq9615 eq140
    | (have r₁ := eq140 y y
       have r₂ := eq9615
       grind)
    | exact resolve eq140 eq9615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq11154 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq9615
  have eq11155 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq11150
  have eq12205 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1516 y y
       have i₂ := eq11155
       grind)
    | exact superpose eq11155 eq1516
    | (have j0 := eq1516 y y
       grind)
    | exact resolve eq1516 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516 eq11155
  have eq12210 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq12205
  have eq21702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1500
       have i₂ := eq681 x y
       grind)
    | exact superpose eq681 eq1500
    | (have j1 := eq681 x y
       grind)
    | (have r₁ := eq1500
       have r₂ := eq681 x y
       grind)
    | exact resolve eq1500 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq1500
  have eq21711 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq21702
  have eq21964 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21711
       grind)
    | exact superpose eq21711 eq14
    | exact resolve eq14 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21977 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 (σ x) y
       have i₂ := eq21711
       grind)
    | exact superpose eq21711 eq52
    | (have j0 := eq52 (σ x) y
       grind)
    | exact resolve eq52 eq21711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq21711
  have eq22020 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21977
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq21977
    | exact resolve eq21977 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21977
  have eq22042 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22020
       have i₂ := eq8999
       grind)
    | exact superpose eq8999 eq22020
    | exact resolve eq22020 eq8999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8999 eq22020
  have eq22047 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22042
       have r₂ := eq11154
       grind)
    | exact resolve eq22042 eq11154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11154 eq22042
  have eq22402 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21964
       have i₂ := eq9612
       grind)
    | exact superpose eq9612 eq21964
    | exact resolve eq21964 eq9612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9612 eq21964
  have eq22404 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq22402
  have eq24130 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12210
       have i₂ := eq22047
       grind)
    | exact superpose eq22047 eq12210
    | exact resolve eq12210 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12210 eq22047
  have eq24201 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq24130
  have eq24231 : x = (M.op y y) := by
    first
    | (have r₁ := eq24201
       have r₂ := eq22404
       grind)
    | exact resolve eq24201 eq22404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22404 eq24201
  have eq24703 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq8
    | exact resolve eq8 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24705 : x = (M.op x y) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq19
    | exact resolve eq19 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq24706 : ∀ X0 : G, y = (M.op y (M.op X0 x)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq28 y y x
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq28
    | exact resolve eq28 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq29170 : y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq24703 y
       have i₂ := eq24706 y
       grind)
    | exact superpose eq24706 eq24703
    | exact resolve eq24703 eq24706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24703 eq24706
  have eq29206 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq29170
       have i₂ := eq24231
       grind)
    | exact superpose eq24231 eq29170
    | exact resolve eq29170 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24231 eq29170
  have eq29879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1014 y y
       have i₂ := eq29206
       grind)
    | exact superpose eq29206 eq1014
    | exact resolve eq1014 eq29206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq29206
  have eq29899 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq29879
       have r₂ := eq9614
       grind)
    | exact resolve eq29879 eq9614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29879
  have eq30555 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq29899
       grind)
    | exact superpose eq29899 eq14
    | exact resolve eq14 eq29899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29899
  have eq30622 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq30555
       have i₂ := eq24705
       grind)
    | exact superpose eq24705 eq30555
    | exact resolve eq30555 eq24705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30555
  have eq30623 : x = y := by grind
  clear eq30622
  have eq31245 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq14
    | exact resolve eq14 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31253 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9614
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq9614
    | exact resolve eq9614 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9614
  have eq31290 : x = (M.op x x) := by
    first
    | (have i₁ := eq24705
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq24705
    | exact resolve eq24705 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24705 eq30623
  have eq31303 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31253
  have eq31309 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31245
       have i₂ := eq31290
       grind)
    | exact superpose eq31290 eq31245
    | exact resolve eq31245 eq31290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31245 eq31290
  have eq31310 : False := by grind
  exact eq31310

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation433 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law433 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq109 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq109 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq113 (σ X0) (σ X1)
       grind)
    | exact superpose eq113 eq13
    | exact resolve eq13 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq129
    | exact resolve eq129 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq129
  have eq1291 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq136 x y
       grind)
    | exact superpose eq136 eq14
    | (have r₁ := eq14
       have r₂ := eq136 x y
       grind)
    | exact resolve eq14 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1320 : False := by grind
  exact eq1320

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxy_pyx_Equation433 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law433 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X0) X0
       have i₂ := eq23 X2 X0
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq11
    | (have r₁ := eq11 X1 (M.op X0 X1)
       have r₂ := eq23 X0 X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq114 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq142 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq8
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq8 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq23
    | (have j1 := eq38 (k X0 X1) X0
       grind)
    | exact resolve eq23 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq23
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq23 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq176 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op X1 (σ X0))
       have i₂ := eq30 (σ X0) X1
       grind)
    | exact superpose eq30 eq56
    | exact resolve eq56 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq191 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq176
    | exact resolve eq176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq219 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq27 X2 X0 X1
       grind)
    | exact superpose eq27 eq23
    | exact resolve eq23 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq936 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq983 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq936
    | (have j0 := eq936 X0 X1
       grind)
    | exact resolve eq936 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1280 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq146 (τ X0) (τ X1)
       have i₂ := eq114 X1 X0
       grind)
    | exact superpose eq114 eq146
    | (have j0 := eq146 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq146 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq146
  have eq1323 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1280 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1280
    | (have j0 := eq1280 X0 X1
       grind)
    | exact resolve eq1280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1332 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1323 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1323
    | (have j0 := eq1323 X0 X1
       grind)
    | exact resolve eq1323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1333 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1332 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1332
    | (have j0 := eq1332 X0 X1
       grind)
    | exact resolve eq1332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1334 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1333 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1333
    | (have j0 := eq1333 X0 X1
       grind)
    | exact resolve eq1333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1345 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1334 X0 (τ (M.op X1 (σ X0)))
       have i₂ := eq191 X0 X1
       grind)
    | exact superpose eq191 eq1334
    | (have j0 := eq1334 X0 (τ (M.op X1 (σ X0)))
       grind)
    | exact resolve eq1334 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq1334
  have eq1401 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq155 y x
       grind)
    | exact superpose eq155 eq14
    | (have j1 := eq155 y x
       grind)
    | exact resolve eq14 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq1787 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op X1 (σ X0)))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 X0 (M.op X2 X0) X1
       have i₂ := eq30 X0 X2
       grind)
    | exact superpose eq30 eq142
    | (have j0 := eq142 X0 (M.op X2 X0) X2
       grind)
    | exact resolve eq142 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq142
  have eq1898 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1787 X0 X1 X2
       have i₂ := eq23 X1 (σ X0)
       grind)
    | exact superpose eq23 eq1787
    | (have j0 := eq1787 X0 X1 X2
       grind)
    | exact resolve eq1787 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq5664 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1898 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1898
    | (have j0 := eq1898 (M.op X1 (τ X0)) X0 X2
       grind)
    | exact resolve eq1898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq9910 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1401
       have i₂ := eq983 x y
       grind)
    | exact superpose eq983 eq1401
    | (have j1 := eq983 (σ y) (σ x)
       grind)
    | (have r₁ := eq1401
       have r₂ := eq983 x y
       grind)
    | exact resolve eq1401 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq1401
  have eq9911 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq9910
  have eq16410 : y = (M.op y (τ (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1345 y (σ x)
       have i₂ := eq9911
       grind)
    | exact superpose eq9911 eq1345
    | (have j0 := eq1345 y x
       grind)
    | exact resolve eq1345 eq9911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq9911
  have eq16510 : y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16410
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq16410
    | exact resolve eq16410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16410
  have eq16511 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq16510
  have eq17409 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op y (M.op X0 y)) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq219 X0 y y
       have i₂ := eq16511
       grind)
    | exact superpose eq16511 eq219
    | exact resolve eq219 eq16511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq16511
  have eq17480 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq17409 X0
       have i₂ := eq23 X0 y
       grind)
    | exact superpose eq23 eq17409
    | exact resolve eq17409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17409
  have eq22040 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq17480 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq22041 : y = (M.op y x) := by grind
  clear eq22040
  have eq22388 : x = (M.op x y) := by
    first
    | (have i₁ := eq23 y x
       have i₂ := eq22041
       grind)
    | exact superpose eq22041 eq23
    | exact resolve eq23 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105846 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (σ (M.op X2 (τ X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq5664 X1 X2 X0
       grind)
    | exact superpose eq5664 eq23
    | (have j1 := eq5664 X1 X2 X2
       grind)
    | exact resolve eq23 eq5664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5664
  have eq125406 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq105846 (σ (M.op X1 (τ X0))) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105846
  have eq125407 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq125406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125406
  have eq126817 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq125407 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq125407
    | exact resolve eq125407 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125407
  have eq128374 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq126817 x y
       have i₂ := eq22041
       grind)
    | exact superpose eq22041 eq126817
    | exact resolve eq126817 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22041 eq126817
  have eq129876 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq128374
       grind)
    | exact superpose eq128374 eq14
    | exact resolve eq14 eq128374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128374
  have eq130150 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq129876
       have i₂ := eq22388
       grind)
    | exact superpose eq22388 eq129876
    | exact resolve eq129876 eq22388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22388 eq129876
  have eq130151 : False := by grind
  exact eq130151

/-- `Equation4331`: `x ◇ (y ◇ x) = z ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4331 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4331 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4331.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X2 X3
       have i₂ := eq8 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X2 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X0 X0
       have i₂ := eq8 X0 X0 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  clear eq15
  have eq37 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq142 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq37 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq37 eq13
    | (have j1 := eq37 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq285 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X1 X1) X2 X3
       have i₂ := eq17 X2 X1 X1 X0
       grind)
    | (have i₁ := eq23 X2 X2 X2
       have i₂ := eq17 X0 X1 X2 X2
       grind)
    | exact superpose eq17 eq23
    | exact resolve eq23 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq23
  have eq351 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq285 x X1 X3 X2
       grind)
    | (have i₁ := eq8 X0 X3 X3
       have i₂ := eq285 X0 X1 X3 X3
       grind)
    | exact superpose eq285 eq8
    | exact resolve eq8 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1104 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq35 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1104 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1104 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1971 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1163 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1163
    | (have j0 := eq1163 (τ X0) X1
       grind)
    | exact resolve eq1163 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1980 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1971 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1971
    | (have j0 := eq1971 X0 X1
       grind)
    | exact resolve eq1971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1985 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1980 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1980
    | (have j0 := eq1980 X0 X1
       grind)
    | exact resolve eq1980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2004 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1985 (τ X0) X1
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq1985
    | (have j0 := eq1985 (τ X0) X1
       grind)
    | exact resolve eq1985 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1985
  have eq2804 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2929 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2804 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2804
    | (have j0 := eq2804 X0 X1
       grind)
    | exact resolve eq2804 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq11293 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1159 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1159
    | (have j0 := eq1159 (τ X0)
       grind)
    | exact resolve eq1159 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq11319 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11293 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11293
    | (have j0 := eq11293 X0
       grind)
    | exact resolve eq11293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11293
  have eq11332 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11319 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11319
    | (have j0 := eq11319 X0
       grind)
    | exact resolve eq11319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11319
  have eq12468 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq142 x y X0
       grind)
    | exact superpose eq142 eq14
    | (have j1 := eq142 X0 y X0
       grind)
    | exact resolve eq14 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq197594 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12468 X0
       have i₂ := eq2929 x y
       grind)
    | exact superpose eq2929 eq12468
    | (have j0 := eq12468 X0
       have j1 := eq2929 X0 y
       grind)
    | (have r₁ := eq12468 X0
       have r₂ := eq2929 x y
       grind)
    | exact resolve eq12468 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929 eq12468
  have eq197596 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq197594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197594
  have eq200521 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2004 (σ y) X0
       have i₂ := eq197596 (σ y)
       grind)
    | exact superpose eq197596 eq2004
    | (have j0 := eq2004 (σ y) X0
       grind)
    | exact resolve eq2004 eq197596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq197596
  have eq200558 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq200521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200521
  have eq200574 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq200558 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq200558
    | exact resolve eq200558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200558
  have eq200585 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq200574 X0
       have j1 := eq11 X0 y
       grind)
    | (have r₁ := eq200574 X0
       have r₂ := eq11 X0 y
       grind)
    | exact resolve eq200574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200574
  have eq203868 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1159 y
       have i₂ := eq200585 y
       grind)
    | exact superpose eq200585 eq1159
    | (have j0 := eq1159 y
       grind)
    | exact resolve eq1159 eq200585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq203872 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11332 y
       have i₂ := eq200585 y
       grind)
    | exact superpose eq200585 eq11332
    | (have j0 := eq11332 y
       grind)
    | (have r₁ := eq11332 y
       have r₂ := eq200585 y
       grind)
    | exact resolve eq11332 eq200585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11332 eq200585
  have eq203929 : y = (M.op y y) := by grind
  clear eq203872
  have eq203933 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq203868
  have eq207183 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq8 y y x
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq8
    | exact resolve eq8 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207247 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 y y
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq351
    | exact resolve eq351 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207370 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq207247 X0 X1
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq207247
    | exact resolve eq207247 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207247
  have eq207381 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq207183 X0
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq207183
    | exact resolve eq207183 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203929 eq207183
  have eq232467 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 (σ y) (σ y)
       have i₂ := eq203933
       grind)
    | exact superpose eq203933 eq351
    | exact resolve eq351 eq203933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq232560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq232467 X0 X1
       have i₂ := eq203933
       grind)
    | exact superpose eq203933 eq232467
    | exact resolve eq232467 eq203933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203933 eq232467
  have eq232697 : y = (σ y) := by
    first
    | (have i₁ := eq232560 x x
       have i₂ := eq207370 x x
       grind)
    | exact superpose eq207370 eq232560
    | exact resolve eq232560 eq207370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207370 eq232560
  have eq233940 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq232697
       grind)
    | exact superpose eq232697 eq14
    | exact resolve eq14 eq232697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233994 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq233940
       have i₂ := eq207381 (σ x)
       grind)
    | exact superpose eq207381 eq233940
    | exact resolve eq233940 eq207381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233940
  have eq234001 : y ≠ (σ y) := by
    first
    | (have i₁ := eq233994
       have i₂ := eq207381 x
       grind)
    | exact superpose eq207381 eq233994
    | exact resolve eq233994 eq207381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207381 eq233994
  have eq234002 : False := by grind
  exact eq234002
