import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3620`: `x ◇ y = z ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation3620 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3620 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3620.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X1) X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X3 X1) X0) X3
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) X3) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op (M.op X2 X3) X1) X0) X3 X2
       have i₂ := eq8 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq80 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X0
       have i₂ := eq18 X1 X2 X0 X0
       grind)
    | (have i₁ := eq8 X2 X1 X0
       have i₂ := eq18 X0 X1 X2 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) X4) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X0 X2) X1) X4 X3
       have i₂ := eq18 X1 X2 (M.op X3 X4) X0
       grind)
    | (have i₁ := eq8 (M.op (M.op X0 X1) X2) X1 X2
       have i₂ := eq18 X0 X1 X2 (M.op X2 X1)
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 X1
       have i₂ := eq18 X1 X2 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq18 X0 X1 x x
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq224 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X2) X1) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq80 X3 (M.op (M.op X0 X3) X2) X1
       have i₂ := eq19 X1 X2 X0 X3
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq30 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq30
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X0 X2
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X0 X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq329 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op (M.op (M.op (M.op X0 X1) X0) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq85 X3 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq85 (M.op (M.op (M.op X0 X1) X0) X2) X0 X1
       grind)
    | exact superpose eq85 eq85
    | exact resolve eq85 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X4 X3 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq85 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X1 X2
       grind)
    | exact superpose eq85 eq19
    | exact resolve eq19 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq348 X0 X1 X2 X3 X4
       have i₂ := eq224 (M.op X0 (M.op (M.op X1 X2) X1)) X2 X4 X3
       grind)
    | exact superpose eq224 eq348
    | exact resolve eq348 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq372 : ∀ X0 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq329 X0 x X2 X3
       have i₂ := eq19 X2 X0 X0 x
       grind)
    | exact superpose eq19 eq329
    | exact resolve eq329 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq329
  have eq382 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 X2) (M.op X2 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq361 X0 x X2 X3 X4
       have i₂ := eq85 X0 x X2
       grind)
    | exact superpose eq85 eq361
    | exact resolve eq361 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq557 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X3 X1) X0) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq372 (M.op (M.op X3 X1) X0) X3 X2
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq372
    | exact resolve eq372 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 (M.op X0 X2)) X2 X0
       have i₂ := eq372 (M.op X0 X2) X1 X0
       grind)
    | exact superpose eq372 eq8
    | exact resolve eq8 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq638 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq557 x X1 X2 X3
       have i₂ := eq382 (M.op X3 X1) x X2 X1
       grind)
    | exact superpose eq382 eq557
    | exact resolve eq557 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq557
  have eq710 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq584 X2 (M.op X1 (M.op X0 (M.op X2 X3))) X3
       have i₂ := eq584 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq584 eq584
    | exact resolve eq584 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq1183 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq638
  have eq4843 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1183 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq1183 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq1183
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq1183 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4858 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq303 (M.op X0 X0)
       have i₂ := eq1183 X0
       grind)
    | exact superpose eq1183 eq303
    | (have j0 := eq303 (M.op X0 X0)
       grind)
    | exact resolve eq303 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4863 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4858
  have eq5024 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq4843 X0 X1
       grind)
    | exact superpose eq4843 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq4843 X0 X1
       grind)
    | exact resolve eq12 eq4843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4843
  have eq5054 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5024 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq276
       have i₂ := eq5054 y x
       grind)
    | exact superpose eq5054 eq276
    | (have j1 := eq5054 y x
       grind)
    | exact resolve eq276 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5599 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq276
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq276
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq276 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq5600 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq5599
  have eq5604 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq5595
  have eq5617 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq5600
  have eq5658 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5617
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq5617
    | exact resolve eq5617 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617
  have eq6113 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq5658
       grind)
    | exact superpose eq5658 eq9
    | exact resolve eq9 eq5658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5658
  have eq6144 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6113
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6113
    | exact resolve eq6113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq6272 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6144
       grind)
    | exact superpose eq6144 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6144
  have eq6273 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6272
  have eq7096 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq6273
       grind)
    | exact superpose eq6273 eq8
    | exact resolve eq8 eq6273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14462 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq264
    | (have j0 := eq264 X1 (τ X0)
       grind)
    | exact resolve eq264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq14541 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14462 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq14462
    | (have j0 := eq14462 X0 X1
       grind)
    | exact resolve eq14462 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14462
  have eq14549 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14541 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14541
    | (have j0 := eq14541 X0 X1
       grind)
    | exact resolve eq14541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14541
  have eq23877 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1183 (σ x)
       have i₂ := eq5604
       grind)
    | exact superpose eq5604 eq1183
    | exact resolve eq1183 eq5604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq5604
  have eq23949 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23877
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq23877
    | exact resolve eq23877 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23877
  have eq27727 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq23949
       grind)
    | exact superpose eq23949 eq9
    | exact resolve eq9 eq23949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23949
  have eq27770 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27727
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27727
    | exact resolve eq27727 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27727
  have eq27771 : y = (k y y) := by
    first
    | (have j1 := eq46 y y
       grind)
    | (have r₁ := eq27770
       have r₂ := eq46 y y
       grind)
    | exact resolve eq27770 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq27770
  have eq31532 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq303 y
       have i₂ := eq27771
       grind)
    | exact superpose eq27771 eq303
    | (have j0 := eq303 y
       grind)
    | exact resolve eq303 eq27771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq31539 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5054 y y
       have i₂ := eq27771
       grind)
    | exact superpose eq27771 eq5054
    | (have j0 := eq5054 y x
       grind)
    | exact resolve eq5054 eq27771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5054
  have eq31540 : y = (M.op y y) := by grind
  clear eq31539
  have eq31542 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq31532
  have eq36819 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq80 X0 y y
       have i₂ := eq31540
       grind)
    | exact superpose eq31540 eq80
    | exact resolve eq80 eq31540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36821 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op y (M.op X2 X1)))) = (M.op (M.op (M.op X0 y) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X0 y y X2 X1
       have i₂ := eq31540
       grind)
    | exact superpose eq31540 eq84
    | exact resolve eq84 eq31540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq36871 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op y (M.op X2 X1)))) = (M.op y (M.op X0 (M.op X1 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36821 X0 X1 X2
       have i₂ := eq224 X0 X1 y y
       grind)
    | exact superpose eq224 eq36821
    | exact resolve eq36821 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq36821
  have eq36888 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op y (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq36871 X0 X1 x
       have i₂ := eq710 y X0 x X1
       grind)
    | exact superpose eq710 eq36871
    | exact resolve eq36871 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq36871
  have eq51644 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq286 y X0
       have i₂ := eq31542
       grind)
    | exact superpose eq31542 eq286
    | (have j0 := eq286 y X0
       grind)
    | exact resolve eq286 eq31542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq51765 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq51644 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq51644
    | (have j0 := eq51644 X0
       grind)
    | exact resolve eq51644 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51644
  have eq71177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq288
  have eq102339 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq4863 X0
       grind)
    | exact superpose eq4863 eq80
    | exact resolve eq80 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4863
  have eq120242 : (M.op y (M.op y y)) = (M.op (M.op y x) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36888 x y
       have i₂ := eq7096 y
       grind)
    | exact superpose eq7096 eq36888
    | exact resolve eq36888 eq7096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7096 eq36888
  have eq120305 : y = (M.op (M.op y x) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120242
       have i₂ := eq36819 y
       grind)
    | exact superpose eq36819 eq120242
    | exact resolve eq120242 eq36819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36819 eq120242
  have eq121168 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq85 X0 y x
       have i₂ := eq120305
       grind)
    | exact superpose eq120305 eq85
    | exact resolve eq85 eq120305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq120305
  have eq122432 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6273
       have i₂ := eq121168 x
       grind)
    | exact superpose eq121168 eq6273
    | exact resolve eq6273 eq121168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6273 eq121168
  have eq122500 : y = (M.op x x) := by grind
  clear eq122432
  have eq124201 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq122500
       grind)
    | exact superpose eq122500 eq8
    | exact resolve eq8 eq122500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129357 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq124201 y
       have i₂ := eq31540
       grind)
    | exact superpose eq31540 eq124201
    | exact resolve eq124201 eq31540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31540 eq124201
  have eq202307 : ∀ X0 : G, y = X0 ∨ (k y X0) = (M.op y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq27771
       have i₂ := eq14549 y X0
       grind)
    | (have i₁ := eq27771
       have i₂ := eq14549 X0 (k y y)
       grind)
    | exact superpose eq14549 eq27771
    | (have j1 := eq14549 y X0
       grind)
    | exact resolve eq27771 eq14549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14549 eq27771
  have eq202319 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq202307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202307
  have eq202340 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq202319 (τ X0)
       grind)
    | exact superpose eq202319 eq17
    | (have j1 := eq202319 (τ X0)
       grind)
    | exact resolve eq17 eq202319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202319
  have eq244223 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq202340 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq202340
    | exact resolve eq202340 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202340
  have eq244226 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq244223 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq244223
    | (have j0 := eq244223 X0
       grind)
    | exact resolve eq244223 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244223
  have eq245019 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq71177 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71177
  have eq245020 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq245019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245019
  have eq245024 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq245020 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq245020
    | exact resolve eq245020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245100 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op (σ (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0) (σ X0)
       have i₂ := eq245020 X0
       grind)
    | exact superpose eq245020 eq8
    | exact resolve eq8 eq245020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245020
  have eq245195 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq245024 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq245024
    | exact resolve eq245024 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq245024
  have eq245209 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq245195 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq245195
    | exact resolve eq245195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245195
  have eq247783 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245100 X0 X1
       have i₂ := eq245209 X0
       grind)
    | exact superpose eq245209 eq245100
    | exact resolve eq245100 eq245209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245100 eq245209
  have eq251706 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq247783 x X0
       have i₂ := eq122500
       grind)
    | exact superpose eq122500 eq247783
    | exact resolve eq247783 eq122500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122500
  have eq251743 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102339 X0 (σ X0)
       have i₂ := eq247783 X0 (σ X0)
       grind)
    | exact superpose eq247783 eq102339
    | exact resolve eq102339 eq247783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102339 eq247783
  have eq252129 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq251706 (σ y)
       have i₂ := eq31542
       grind)
    | exact superpose eq31542 eq251706
    | exact resolve eq251706 eq31542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31542 eq251706
  have eq252427 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq51765 x
       have i₂ := eq252129
       grind)
    | exact superpose eq252129 eq51765
    | (have j0 := eq51765 x
       grind)
    | exact resolve eq51765 eq252129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51765 eq252129
  have eq257315 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq252427
       grind)
    | exact superpose eq252427 eq14
    | exact resolve eq14 eq252427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252427
  have eq257415 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq257315
       have i₂ := eq244226 x
       grind)
    | exact superpose eq244226 eq257315
    | (have j1 := eq244226 x
       grind)
    | exact resolve eq257315 eq244226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244226 eq257315
  have eq257421 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by grind
  clear eq257415
  have eq257432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq257421
       have i₂ := eq129357
       grind)
    | exact superpose eq129357 eq257421
    | exact resolve eq257421 eq129357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129357 eq257421
  have eq257433 : x = y := by grind
  clear eq257432
  have eq257471 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq257433
       grind)
    | exact superpose eq257433 eq14
    | exact resolve eq14 eq257433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257433
  have eq257737 : False := by grind
  exact eq257737

/-- `Equation3620`: `x ◇ y = z ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3620 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3620 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3620.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X1) X0)) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X3 X1) X0) X3
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) X3) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op (M.op X2 X3) X1) X0) X3 X2
       have i₂ := eq8 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq16
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq81 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X0
       have i₂ := eq18 X1 X2 X0 X0
       grind)
    | (have i₁ := eq8 X2 X1 X0
       have i₂ := eq18 X0 X1 X2 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 X1
       have i₂ := eq18 X1 X2 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq18 X0 X1 x x
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq105 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq154 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq168 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq154 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq154
    | exact resolve eq154 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq254 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq433 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X2) X1) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq81 X3 (M.op (M.op X0 X3) X2) X1
       have i₂ := eq19 X1 X2 X0 X3
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op (M.op (M.op (M.op X0 X1) X0) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 X3 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq86 (M.op (M.op (M.op X0 X1) X0) X2) X0 X1
       grind)
    | exact superpose eq86 eq86
    | exact resolve eq86 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X4 X3 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq86 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X3) X4) X1 X2
       grind)
    | exact superpose eq86 eq19
    | exact resolve eq19 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq515 X0 X1 X2 X3 X4
       have i₂ := eq433 (M.op X0 (M.op (M.op X1 X2) X1)) X2 X4 X3
       grind)
    | exact superpose eq433 eq515
    | exact resolve eq515 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq515
  have eq547 : ∀ X0 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq490 X0 x X2 X3
       have i₂ := eq19 X2 X0 X0 x
       grind)
    | exact superpose eq19 eq490
    | exact resolve eq490 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq490
  have eq559 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X3 (M.op (M.op X0 X2) (M.op X2 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq530 X0 x X2 X3 X4
       have i₂ := eq86 X0 x X2
       grind)
    | exact superpose eq86 eq530
    | exact resolve eq530 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq530
  have eq575 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X3 X1) X0) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq547 (M.op (M.op X3 X1) X0) X3 X2
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq547
    | exact resolve eq547 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq547 (M.op X1 X2) X0 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq547 eq81
    | exact resolve eq81 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq656 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq575 x X1 X2 X3
       have i₂ := eq559 (M.op X3 X1) x X2 X1
       grind)
    | exact superpose eq559 eq575
    | exact resolve eq575 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq575
  have eq1230 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq656
  have eq4976 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1230 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq1230 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq1230
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq1230 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4992 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq292 (M.op X0 X0)
       have i₂ := eq1230 X0
       grind)
    | exact superpose eq1230 eq292
    | (have j0 := eq292 (M.op X0 X0)
       grind)
    | exact resolve eq292 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4997 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4992 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4992
  have eq5103 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq4976 X0 X1
       grind)
    | exact superpose eq4976 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq4976 X0 X1
       grind)
    | exact resolve eq12 eq4976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4976
  have eq5133 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5103
  have eq5408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq266
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq266
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq5409 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq5408
  have eq6067 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq168 x
       have i₂ := eq5409
       grind)
    | exact superpose eq5409 eq168
    | exact resolve eq168 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq6070 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1230 (σ x)
       have i₂ := eq5409
       grind)
    | exact superpose eq5409 eq1230
    | exact resolve eq1230 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5409
  have eq6113 : (σ y) = (σ (k y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6070
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq6070
    | exact resolve eq6070 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070
  have eq6114 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6067
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6067
    | exact resolve eq6067 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067
  have eq6245 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6114
       grind)
    | exact superpose eq6114 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114
  have eq6246 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6245
  have eq7061 : ∀ X0 : G, x = (M.op X0 (M.op x X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq81 X0 x y
       have i₂ := eq6246
       grind)
    | exact superpose eq6246 eq81
    | exact resolve eq81 eq6246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9493 : (k y y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq6113
       grind)
    | exact superpose eq6113 eq9
    | exact resolve eq9 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq9528 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9493
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9493
    | exact resolve eq9493 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9493
  have eq10603 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq9528
       grind)
    | exact superpose eq9528 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq9528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9528
  have eq10604 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq10603
  have eq13012 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq81 X0 y y
       have i₂ := eq10604
       grind)
    | exact superpose eq10604 eq81
    | exact resolve eq81 eq10604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq10604
  have eq13935 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7061 y
       have i₂ := eq6246
       grind)
    | exact superpose eq6246 eq7061
    | exact resolve eq7061 eq6246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6246 eq7061
  have eq14045 : x = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq13935
  have eq14167 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq254
    | (have j0 := eq254 X1 (τ X0)
       grind)
    | exact resolve eq254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq14258 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14167 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq14167
    | (have j0 := eq14167 X0 X1
       grind)
    | exact resolve eq14167 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq14167
  have eq14268 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14258 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14258
    | (have j0 := eq14258 X0 X1
       grind)
    | exact resolve eq14258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14258
  have eq16970 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13012 x
       have i₂ := eq14045
       grind)
    | exact superpose eq14045 eq13012
    | exact resolve eq13012 eq14045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13012 eq14045
  have eq17093 : y = (M.op x x) := by grind
  clear eq16970
  have eq17990 : y = (k y y) := by
    first
    | (have i₁ := eq1230 x
       have i₂ := eq17093
       grind)
    | exact superpose eq17093 eq1230
    | exact resolve eq1230 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq17992 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq17093
       grind)
    | exact superpose eq17093 eq8
    | exact resolve eq8 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18345 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq292 y
       have i₂ := eq17990
       grind)
    | exact superpose eq17990 eq292
    | (have j0 := eq292 y
       grind)
    | exact resolve eq292 eq17990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq18349 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5133 y y
       have i₂ := eq17990
       grind)
    | exact superpose eq17990 eq5133
    | (have j0 := eq5133 y x
       grind)
    | exact resolve eq5133 eq17990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5133
  have eq18350 : y = (M.op y y) := by grind
  clear eq18349
  have eq18352 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq18345
  have eq22561 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq275 y X0
       have i₂ := eq18352
       grind)
    | exact superpose eq18352 eq275
    | (have j0 := eq275 y X0
       grind)
    | exact resolve eq275 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq22655 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq22561 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22561
    | (have j0 := eq22561 X0
       grind)
    | exact resolve eq22561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22561
  have eq22966 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq17992 y
       have i₂ := eq18350
       grind)
    | exact superpose eq18350 eq17992
    | exact resolve eq17992 eq18350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17992 eq18350
  have eq238834 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq4997 X0
       grind)
    | exact superpose eq4997 eq605
    | exact resolve eq605 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq4997
  have eq243617 : ∀ X0 : G, y = X0 ∨ (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq17990
       have i₂ := eq14268 y X0
       grind)
    | (have i₁ := eq17990
       have i₂ := eq14268 X0 (k y y)
       grind)
    | exact superpose eq14268 eq17990
    | (have j1 := eq14268 y X0
       grind)
    | exact resolve eq17990 eq14268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14268 eq17990
  have eq243625 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq243617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243617
  have eq295111 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq238834 (τ X0) X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq238834
    | (have j1 := eq105 X0
       grind)
    | exact resolve eq238834 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq238834
  have eq295115 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq295111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295111
  have eq295120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq295115 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq295115
    | exact resolve eq295115 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295115
  have eq295383 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0) (σ X0)
       have i₂ := eq295120 X0
       grind)
    | exact superpose eq295120 eq8
    | exact resolve eq8 eq295120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297599 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq295383 x X0
       have i₂ := eq17093
       grind)
    | exact superpose eq17093 eq295383
    | exact resolve eq295383 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17093 eq295383
  have eq297831 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq297599 (σ y)
       have i₂ := eq18352
       grind)
    | exact superpose eq18352 eq297599
    | exact resolve eq297599 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18352 eq297599
  have eq298402 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq22655 x
       have i₂ := eq297831
       grind)
    | exact superpose eq297831 eq22655
    | (have j0 := eq22655 x
       grind)
    | exact resolve eq22655 eq297831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22655 eq297831
  have eq306088 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq298402
       grind)
    | exact superpose eq298402 eq14
    | exact resolve eq14 eq298402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298402
  have eq306181 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq306088
       have i₂ := eq243625 x
       grind)
    | exact superpose eq243625 eq306088
    | (have j1 := eq243625 x
       grind)
    | exact resolve eq306088 eq243625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243625 eq306088
  have eq306196 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by grind
  clear eq306181
  have eq306221 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq306196
       have i₂ := eq22966
       grind)
    | exact superpose eq22966 eq306196
    | exact resolve eq306196 eq22966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22966 eq306196
  have eq306222 : x = y := by grind
  clear eq306221
  have eq306275 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq306222
       grind)
    | exact superpose eq306222 eq14
    | exact resolve eq14 eq306222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306222
  have eq306491 : False := by grind
  exact eq306491

/-- `Equation3634`: `x ◇ y = z ◇ ((w ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3634 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3634 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3634.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq19 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op (M.op X3 X0) X1) X4 x
       have i₂ := eq8 X0 X1 (M.op x X2) X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq19 X0 X1 x x X4
       have i₂ := eq8 X0 X1 x x
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq83 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq17
  have eq218 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq83
  have eq233 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq218
    | exact resolve eq218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq543 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) (σ X0) x
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq21
    | (have j1 := eq41 X1 X0
       grind)
    | exact resolve eq21 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1566 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq552 (M.op X0 X1)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq552
    | (have j0 := eq552 (M.op X0 X1)
       grind)
    | exact resolve eq552 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq552
  have eq1573 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1566 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1639 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1742 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1639 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1639
    | (have j0 := eq1639 X0 X1
       grind)
    | exact resolve eq1639 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq1898 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq1573 X0 X1
       grind)
    | exact superpose eq1573 eq21
    | exact resolve eq21 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq2595 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1898 X1 X1 X2
       have i₂ := eq1742 X0 X1
       grind)
    | (have i₁ := eq1898 X0 X1 X2
       have i₂ := eq1742 (M.op X0 X1) X1
       grind)
    | exact superpose eq1742 eq1898
    | (have j1 := eq1742 X0 X1
       grind)
    | exact resolve eq1898 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742 eq1898
  have eq3442 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq543 y x X0
       grind)
    | exact superpose eq543 eq14
    | (have j1 := eq543 y x X0
       grind)
    | exact resolve eq14 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq3486 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq3442 X0
       have j1 := eq2595 y x X0
       grind)
    | (have r₁ := eq3442 X0
       have r₂ := eq2595 y x x
       grind)
    | exact resolve eq3442 eq2595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595 eq3442
  have eq3551 : y = (k y (τ (σ y))) := by
    first
    | (have i₁ := eq233 y
       have i₂ := eq3486 (σ y)
       grind)
    | exact superpose eq3486 eq233
    | exact resolve eq233 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq3555 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3486 (σ x)
       grind)
    | exact superpose eq3486 eq14
    | exact resolve eq14 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3558 : y = (k y y) := by
    first
    | (have i₁ := eq3551
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3551
    | exact resolve eq3551 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551
  have eq3673 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq3558
       grind)
    | exact superpose eq3558 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq3558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq3679 : y = (M.op y y) := by grind
  clear eq3673
  have eq3727 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq21 y y x
       have i₂ := eq3679
       grind)
    | exact superpose eq3679 eq21
    | exact resolve eq21 eq3679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3679
  have eq4096 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3555
       have i₂ := eq3727 x
       grind)
    | exact superpose eq3727 eq3555
    | exact resolve eq3555 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555 eq3727
  have eq4100 : False := by grind
  exact eq4100

/-- `Equation3666`: `x ◇ x = (x ◇ y) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyy_pyx_pxy_Equation3666 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3666 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq13
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq159 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X1)
       have i₂ := eq68 X0 X1
       grind)
    | (have i₁ := eq9 (M.op X0 X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq9
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq944 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq906 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq906
    | (have j0 := eq906 X0 X1
       grind)
    | exact resolve eq906 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq1933 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1984 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1933 (σ X1) (σ X0)
       grind)
    | exact superpose eq1933 eq13
    | (have j1 := eq1933 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1993 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1984 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1984
    | (have j0 := eq1984 X0 X1
       grind)
    | exact resolve eq1984 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984
  have eq2038 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2083 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2038 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2084 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2038 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq3958 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq944 x y
       grind)
    | exact superpose eq944 eq14
    | (have j1 := eq944 x y
       grind)
    | exact resolve eq14 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq61749 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3958
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq3958
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq3958 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3958
  have eq61761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq61749
  have eq61762 : (M.op x x) = (M.op y y) := by grind
  clear eq61761
  have eq63008 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq61762
       grind)
    | exact superpose eq61762 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq61762
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq61762
       grind)
    | exact resolve eq11 eq61762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81205 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq63008 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63008
  have eq82301 : (M.op x y) = (M.op y x) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq1933 x y
       have i₂ := eq81205
       grind)
    | exact superpose eq81205 eq1933
    | (have j0 := eq1933 x y
       grind)
    | exact resolve eq1933 eq81205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq82302 : (k x y) = (M.op y x) := by
    first
    | (have j1 := eq2084 x y
       grind)
    | (have r₁ := eq82301
       have r₂ := eq2084 x y
       grind)
    | (have r₁ := eq82301
       have r₂ := eq2084 y x
       grind)
    | exact resolve eq82301 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084 eq82301
  have eq321926 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq159 y X0
       have i₂ := eq61762
       grind)
    | exact superpose eq61762 eq159
    | (have j0 := eq159 x X0
       grind)
    | exact resolve eq159 eq61762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq61762
  have eq379067 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq321926 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq321926
    | (have j0 := eq321926 (σ X0)
       grind)
    | (have r₁ := eq321926 (σ x)
       have r₂ := eq42 x
       grind)
    | exact resolve eq321926 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq321926
  have eq379069 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq379067 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq379067
    | (have j0 := eq379067 X0
       grind)
    | exact resolve eq379067 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379067
  have eq472924 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1993 x y
       grind)
    | exact superpose eq1993 eq14
    | (have j1 := eq1993 x y
       grind)
    | exact resolve eq14 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993
  have eq472929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq472924
       have i₂ := eq81205
       grind)
    | exact superpose eq81205 eq472924
    | exact resolve eq472924 eq81205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472924
  have eq472930 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq472929
  have eq472935 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq472930
       have i₂ := eq82302
       grind)
    | exact superpose eq82302 eq472930
    | exact resolve eq472930 eq82302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472930
  have eq472943 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq472935
       grind)
    | exact superpose eq472935 eq14
    | exact resolve eq14 eq472935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550920 : (σ (k x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have j0 := eq379069 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379069
  have eq550922 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq550920
       have i₂ := eq82302
       grind)
    | exact superpose eq82302 eq550920
    | exact resolve eq550920 eq82302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82302 eq550920
  have eq551162 : (M.op (σ x) (σ y)) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2083 (σ y) (σ x)
       have i₂ := eq550922
       grind)
    | exact superpose eq550922 eq2083
    | exact resolve eq2083 eq550922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083 eq550922
  have eq551193 : (σ (M.op y x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq551162
       have r₂ := eq472935
       grind)
    | exact resolve eq551162 eq472935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472935 eq551162
  have eq551357 : (σ (M.op y x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq551193
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq551193
    | exact resolve eq551193 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551193
  have eq551464 : (σ (M.op x y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq551357
       have i₂ := eq81205
       grind)
    | exact superpose eq81205 eq551357
    | exact resolve eq551357 eq81205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81205 eq551357
  have eq551509 : False := by grind
  exact eq551509

/-- `Equation3672`: `x ◇ x = (x ◇ y) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_pyy_pxx_pyx_Equation3672 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3672 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3672.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) (M.op X3 X3)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 (M.op X0 X1) (M.op x x) X3
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X0
       have i₂ := eq8 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq24
    | exact resolve eq24 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) ≠ (M.op (M.op X0 X1) (M.op X2 X2)) ∨ (M.op (M.op X0 X1) (M.op X2 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq41 (σ X0)
       grind)
    | exact superpose eq41 eq13
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq46
    | exact resolve eq46 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X3)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq155 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op (σ X0) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq42 (σ X0) X1 X2
       grind)
    | exact superpose eq42 eq13
    | exact resolve eq13 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq165 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 X0 X1 X2
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq155
    | exact resolve eq155 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq155
  have eq199 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X2) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (σ X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq8
    | exact resolve eq8 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 (σ X0) X1 X2
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq27
    | exact resolve eq27 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq73
    | exact resolve eq73 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X1
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq28
    | (have j1 := eq73 X1 X0
       grind)
    | exact resolve eq28 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq73 (τ X0) X1
       grind)
    | exact superpose eq73 eq16
    | (have j1 := eq73 (τ X0) X1
       grind)
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq73
  have eq403 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq345
    | (have j0 := eq345 X0 X1
       grind)
    | exact resolve eq345 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq2987 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X1)) = (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X3 X3)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq165 (M.op X0 X0) X2 X3
       have i₂ := eq65 X0 X1 X0 X0
       grind)
    | exact superpose eq65 eq165
    | (have j1 := eq65 X0 X1 X2 X3
       grind)
    | exact resolve eq165 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq165
  have eq3208 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2987 X0 X1 x x
       have i₂ := eq253 X0 x x
       grind)
    | exact superpose eq253 eq2987
    | (have j0 := eq2987 X0 X1 x x
       grind)
    | exact resolve eq2987 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq2987
  have eq3402 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ (k X0 X1)) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq28
    | (have j1 := eq74 X1 X0
       grind)
    | exact resolve eq28 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3418 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3427 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (M.op (k X0 X1) (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3402 X0 X1
       have i₂ := eq51 (k X0 X1)
       grind)
    | exact superpose eq51 eq3402
    | (have j0 := eq3402 X0 X1
       grind)
    | exact resolve eq3402 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402
  have eq3485 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op (k X0 X1) (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3427 X0 X1
       have i₂ := eq51 X1
       grind)
    | exact superpose eq51 eq3427
    | (have j0 := eq3427 X0 X1
       grind)
    | exact resolve eq3427 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3427
  have eq19225 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq376 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq376
    | exact resolve eq376 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq19643 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19225 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq19225
    | (have j0 := eq19225 X0 X1
       grind)
    | exact resolve eq19225 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19225
  have eq27383 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0)
       have i₂ := eq403 X0 X1
       grind)
    | exact superpose eq403 eq9
    | (have j1 := eq403 X0 X1
       grind)
    | exact resolve eq9 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq27775 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27383 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq27383
    | (have j0 := eq27383 X0 X1
       grind)
    | exact resolve eq27383 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27383
  have eq142969 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3485 X0 X1
       have i₂ := eq357 X0 X1
       grind)
    | exact superpose eq357 eq3485
    | (have j0 := eq3485 X0 X1
       have j1 := eq357 X0 X1
       grind)
    | exact resolve eq3485 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq3485
  have eq143171 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq142969 X0 X1
       have j1 := eq3418 X1 X0
       grind)
    | (have r₁ := eq142969 X1 X0
       have r₂ := eq3418 X0 X1
       grind)
    | exact resolve eq142969 eq3418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142969
  have eq423596 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27775 y x
       grind)
    | exact superpose eq27775 eq14
    | (have j1 := eq27775 y x
       grind)
    | exact resolve eq14 eq27775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27775
  have eq423601 : (k y x) = (M.op y y) := by
    first
    | (have j1 := eq19643 x y
       grind)
    | (have r₁ := eq423596
       have r₂ := eq19643 x y
       grind)
    | exact resolve eq423596 eq19643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19643 eq423596
  have eq423605 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq423601
       grind)
    | exact superpose eq423601 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq423601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423601
  have eq424577 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (σ (M.op X0 X0))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq199 X0 y y
       have i₂ := eq423605
       grind)
    | exact superpose eq423605 eq199
    | exact resolve eq199 eq423605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423605
  have eq424584 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq424577 x
       have i₂ := eq199 x x y
       grind)
    | exact superpose eq199 eq424577
    | exact resolve eq424577 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq424577
  have eq424585 : (M.op x y) = (M.op x x) := by grind
  clear eq424584
  have eq424781 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq143171 y x
       grind)
    | exact superpose eq143171 eq14
    | (have j1 := eq143171 y x
       grind)
    | exact resolve eq14 eq143171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143171
  have eq424788 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq3208 x y
       grind)
    | (have r₁ := eq424781
       have r₂ := eq3208 x y
       grind)
    | exact resolve eq424781 eq3208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208 eq424781
  have eq424790 : (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq424788
       have i₂ := eq424585
       grind)
    | exact superpose eq424585 eq424788
    | exact resolve eq424788 eq424585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424788
  have eq424806 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3418 x y
       have i₂ := eq424790
       grind)
    | exact superpose eq424790 eq3418
    | (have j0 := eq3418 x y
       grind)
    | exact resolve eq3418 eq424790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418 eq424790
  have eq424818 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq424806
  have eq425502 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq424818
       grind)
    | exact superpose eq424818 eq14
    | exact resolve eq14 eq424818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424818
  have eq425784 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq425502
       have i₂ := eq424585
       grind)
    | exact superpose eq424585 eq425502
    | exact resolve eq425502 eq424585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424585 eq425502
  have eq425785 : False := by grind
  exact eq425785

/-- `Equation3673`: `x ◇ x = (x ◇ y) ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3673 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3673 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3673.models_iff G M).mp hM
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq359 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq365 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq359 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq359 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq359 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq359 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq398 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq365 (σ X0) (σ X1)
       grind)
    | exact superpose eq365 eq13
    | exact resolve eq13 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq398 X0 X1
       have i₂ := eq365 X0 X1
       grind)
    | exact superpose eq365 eq398
    | exact resolve eq398 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq398
  have eq1137 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq403 x y
       grind)
    | exact superpose eq403 eq14
    | (have r₁ := eq14
       have r₂ := eq403 x y
       grind)
    | exact resolve eq14 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq1169 : False := by grind
  exact eq1169

/-- `Equation3714`: `x ◇ y = (x ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3714 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3714 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3714.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
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
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq98 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq32 X1 (τ X0)
       grind)
    | exact superpose eq32 eq16
    | (have j1 := eq32 X1 X1
       grind)
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq121 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq106
    | exact resolve eq106 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq131 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X0 X0)
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq30 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X1)
       grind)
    | exact superpose eq12 eq30
    | (have j0 := eq30 X2 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq30 X1 X0 X0
       grind)
    | exact superpose eq30 eq18
    | (have j1 := eq30 X1 X0 x
       grind)
    | exact resolve eq18 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq30
  have eq157 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq147
    | (have j0 := eq147 X0 X1
       grind)
    | exact resolve eq147 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq188 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0
       have i₂ := eq32 (σ X0) X1
       grind)
    | exact superpose eq32 eq121
    | (have j1 := eq32 (σ X0) X1
       grind)
    | exact resolve eq121 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq292 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq34
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq13
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq34 X0 X2
       grind)
    | exact superpose eq34 eq13
    | (have j1 := eq34 X0 X2
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq631 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq204 X0 X1
       grind)
    | exact resolve eq12 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq650 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq631 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq966 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1032 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq966
    | (have j0 := eq966 X0 X1
       grind)
    | exact resolve eq966 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1200 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq10
    | (have j1 := eq37 X0 X1
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1200
    | (have j0 := eq1200 X0 X1
       grind)
    | exact resolve eq1200 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1329 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1329 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1329
    | (have j0 := eq1329 X0 X1
       grind)
    | exact resolve eq1329 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq2009 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq14
    | (have j1 := eq60 x y
       grind)
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2011 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq60 X0 X0
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2457 : ∀ X0 X1 X2 : G, X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1289 X1 X0
       have i₂ := eq650 X0 X2
       grind)
    | exact superpose eq650 eq1289
    | (have j0 := eq1289 X1 X0
       have j1 := eq650 X0 X2
       grind)
    | exact resolve eq1289 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq2522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq305
       have i₂ := eq1379 y x
       grind)
    | exact superpose eq1379 eq305
    | (have j1 := eq1379 y x
       grind)
    | (have r₁ := eq305
       have r₂ := eq1379 y x
       grind)
    | exact resolve eq305 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq305
       have i₂ := eq1289 y x
       grind)
    | exact superpose eq1289 eq305
    | (have j1 := eq1289 (σ y) (σ x)
       grind)
    | (have r₁ := eq305
       have r₂ := eq1289 y x
       grind)
    | exact resolve eq305 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq2524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq305
       have i₂ := eq1032 x y
       grind)
    | exact superpose eq1032 eq305
    | (have j1 := eq1032 x y
       grind)
    | (have r₁ := eq305
       have r₂ := eq1032 x y
       grind)
    | exact resolve eq305 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq2525 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2524
  have eq2526 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2523
  have eq2527 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2522
  have eq2548 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq2525
       grind)
    | exact superpose eq2525 eq20
    | exact resolve eq20 eq2525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525
  have eq2561 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2548
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq2548
    | exact resolve eq2548 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq3152 : ∀ X0 X1 X2 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq32 (σ X0) X2
       grind)
    | exact superpose eq32 eq317
    | (have j0 := eq317 X0 X1
       have j1 := eq32 (σ X0) X2
       grind)
    | exact resolve eq317 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3168 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
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
  have eq3238 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3168 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq3168
    | (have j0 := eq3168 X0 X1
       grind)
    | exact resolve eq3168 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3244 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3152 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3152
    | (have j0 := eq3152 X0 X1 X2
       grind)
    | exact resolve eq3152 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3271 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq2561
       grind)
    | exact superpose eq2561 eq9
    | exact resolve eq9 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq3318 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3271
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3271
    | exact resolve eq3271 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3319 : y = (k y y) := by
    first
    | (have j1 := eq67 y y
       grind)
    | (have r₁ := eq3318
       have r₂ := eq67 y y
       grind)
    | exact resolve eq3318 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq3472 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq338 y
       have i₂ := eq3319
       grind)
    | exact superpose eq3319 eq338
    | (have j0 := eq338 y
       grind)
    | exact resolve eq338 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq3479 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq32 y y
       have i₂ := eq3319
       grind)
    | exact superpose eq3319 eq32
    | (have j0 := eq32 y x
       grind)
    | exact resolve eq32 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3319
  have eq3486 : y = (M.op y y) := by grind
  clear eq3479
  have eq3489 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3472
  have eq3571 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 X0
       have i₂ := eq143 X0 X2 X1
       grind)
    | exact superpose eq143 eq67
    | (have j0 := eq67 X1 X0
       have j1 := eq143 X1 X2 X1
       grind)
    | (have r₁ := eq67 X0 X0
       have r₂ := eq143 X0 X1 X0
       grind)
    | exact resolve eq67 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq143
  have eq3728 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3571 X0 X1 X2
       have j1 := eq28 (k X1 X0) X2 X1
       grind)
    | (have r₁ := eq3571 X0 X2 X2
       have r₂ := eq28 X0 X1 X2
       grind)
    | (have r₁ := eq3571 X2 X0 X2
       have r₂ := eq28 X0 X1 X2
       grind)
    | (have r₁ := eq3571 (M.op X1 X2) (k X1 X2) X2
       have r₂ := eq28 X0 X1 X2
       grind)
    | exact resolve eq3571 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3571
  have eq3736 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq131 X0 y
       have i₂ := eq3486
       grind)
    | exact superpose eq3486 eq131
    | exact resolve eq131 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq3936 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq157 (σ y) x
       have i₂ := eq3489
       grind)
    | exact superpose eq3489 eq157
    | (have j0 := eq157 (σ y) X0
       grind)
    | exact resolve eq157 eq3489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq3489
  have eq7017 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq318 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq318
    | exact resolve eq318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq7199 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7017 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq7017
    | (have j0 := eq7017 X0 X1 X2
       grind)
    | exact resolve eq7017 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017
  have eq7519 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq319
    | exact resolve eq319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq7702 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7519 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq7519
    | (have j0 := eq7519 X0 X1 X2
       grind)
    | exact resolve eq7519 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7519
  have eq7763 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq317 x x
       have i₂ := eq2526
       grind)
    | exact superpose eq2526 eq317
    | exact resolve eq317 eq2526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq7799 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7763
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq7763
    | exact resolve eq7763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7763
  have eq9525 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq121 x
       have i₂ := eq2527
       grind)
    | exact superpose eq2527 eq121
    | exact resolve eq121 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq9584 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9525
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9525
    | exact resolve eq9525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9525
  have eq9585 : x = (k x y) := by grind
  clear eq9584
  have eq33164 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq3238 X0 X1
       grind)
    | exact superpose eq3238 eq25
    | (have j1 := eq3238 X0 X1
       grind)
    | exact resolve eq25 eq3238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq34246 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X0))) = (k (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1
       have i₂ := eq54 (σ X1) X0
       grind)
    | exact superpose eq54 eq121
    | (have j1 := eq54 (σ X1) X0
       grind)
    | exact resolve eq121 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq121
  have eq34562 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ (M.op (σ X1) (σ X0))) = (k (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34246 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34246
    | (have j0 := eq34246 X0 X1
       grind)
    | exact resolve eq34246 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34246
  have eq34683 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34562 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq34562
    | (have j0 := eq34562 X0 X1
       grind)
    | exact resolve eq34562 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34562
  have eq36719 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1253 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq36721 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq36719 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36719
    | (have j0 := eq36719 X0
       grind)
    | exact resolve eq36719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36719
  have eq37122 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq36721 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq36721
    | (have j0 := eq36721 (M.op X0 X0)
       grind)
    | (have r₁ := eq36721 (M.op X0 X0)
       have r₂ := eq20 X0
       grind)
    | exact resolve eq36721 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36721
  have eq37151 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq37122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37122
  have eq58053 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34683 x x
       have i₂ := eq2526
       grind)
    | exact superpose eq2526 eq34683
    | (have j0 := eq34683 x x
       grind)
    | exact resolve eq34683 eq2526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34683
  have eq58131 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq58053
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq58053
    | exact resolve eq58053 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58053
  have eq61383 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq7799
       grind)
    | exact superpose eq7799 eq9
    | exact resolve eq9 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7799
  have eq61396 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq61383
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq61383
    | exact resolve eq61383 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61383
  have eq61468 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq46 x x
       have i₂ := eq61396
       grind)
    | exact superpose eq61396 eq46
    | exact resolve eq46 eq61396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61396
  have eq61493 : y = (M.op x x) ∨ x = y := by grind
  clear eq61468
  have eq62656 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7199 X2 (τ X0) (τ X1)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq7199
    | (have j0 := eq7199 X2 (τ X0) X2
       grind)
    | exact resolve eq7199 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199
  have eq62690 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62656 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq62656
    | (have j0 := eq62656 X0 X1 X2
       grind)
    | exact resolve eq62656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62656
  have eq62696 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62690 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq62690
    | (have j0 := eq62690 X0 X1 X2
       grind)
    | exact resolve eq62690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62690
  have eq62697 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62696 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62696
    | (have j0 := eq62696 X0 X1 X2
       grind)
    | exact resolve eq62696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62696
  have eq62770 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7702 X2 (τ X1) (τ X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq7702
    | (have j0 := eq7702 X2 (τ X1) X2
       grind)
    | exact resolve eq7702 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq7702
  have eq62812 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62770 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62770
    | (have j0 := eq62770 X0 X1 X2
       grind)
    | exact resolve eq62770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62770
  have eq62817 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62812 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq62812
    | (have j0 := eq62812 X0 X1 X2
       grind)
    | exact resolve eq62812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62812
  have eq62818 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62817 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62817
    | (have j0 := eq62817 X0 X1 X2
       grind)
    | exact resolve eq62817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62817
  have eq64493 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq58131
  have eq64511 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq64493
       have r₂ := eq61493
       grind)
    | exact resolve eq64493 eq61493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64493
  have eq67483 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2011 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq67484 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq67483 X0 X1
       have j1 := eq292 X1 X0
       grind)
    | (have r₁ := eq67483 (k X1 X1) X0
       have r₂ := eq292 X0 X1
       grind)
    | (have r₁ := eq67483 X0 (σ (k X1 X1))
       have r₂ := eq292 (σ X0) X1
       grind)
    | (have r₁ := eq67483 X1 X0
       have r₂ := eq292 X0 X1
       grind)
    | exact resolve eq67483 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq67483
  have eq67679 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq67484 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq67484 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq67484 eq16
    | (have j1 := eq67484 (τ X1) X0
       grind)
    | exact resolve eq16 eq67484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67680 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq67484 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq67484 X0 (σ X0)
       grind)
    | exact superpose eq67484 eq9
    | (have j1 := eq67484 X1 X0
       grind)
    | exact resolve eq9 eq67484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67484
  have eq67699 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67679 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq67679
    | (have j0 := eq67679 X0 X1
       grind)
    | exact resolve eq67679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67679
  have eq67706 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67699 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67699
    | (have j0 := eq67699 X0 X1
       grind)
    | exact resolve eq67699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67699
  have eq67717 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq3244 x y X0
       grind)
    | exact superpose eq3244 eq14
    | (have j1 := eq3244 x y X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq3244 (σ (M.op x y)) (M.op (σ x) (σ y)) x
       grind)
    | (have r₁ := eq14
       have r₂ := eq3244 (M.op (σ x) (σ y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq14 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq67720 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq67717 X0
       have j1 := eq2457 x y X0
       grind)
    | (have r₁ := eq67717 X0
       have r₂ := eq2457 (σ (M.op x y)) (σ (k x y)) x
       grind)
    | (have r₁ := eq67717 X0
       have r₂ := eq2457 (σ (k x y)) (σ (M.op x y)) x
       grind)
    | (have r₁ := eq67717 X0
       have r₂ := eq2457 x y x
       grind)
    | exact resolve eq67717 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457 eq67717
  have eq67738 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25 X0 x
       have i₂ := eq67720 X0
       grind)
    | exact superpose eq67720 eq25
    | exact resolve eq25 eq67720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq67759 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq67720 (σ X0)
       grind)
    | exact superpose eq67720 eq13
    | exact resolve eq13 eq67720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67762 : ∀ X0 : G, (k X0 (τ (σ x))) = (τ (M.op (σ X0) (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq42 X0 (σ x)
       have i₂ := eq67720 (σ X0)
       grind)
    | exact superpose eq67720 eq42
    | exact resolve eq42 eq67720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67720
  have eq67775 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ X0) (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq67762 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq67762
    | exact resolve eq67762 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67762
  have eq67951 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq305
       have i₂ := eq67706 y x
       grind)
    | exact superpose eq67706 eq305
    | (have j1 := eq67706 y x
       grind)
    | exact resolve eq305 eq67706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq67952 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2009
       have i₂ := eq67706 y x
       grind)
    | exact superpose eq67706 eq2009
    | (have j1 := eq67706 y x
       grind)
    | exact resolve eq2009 eq67706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009 eq67706
  have eq68133 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq67952
  have eq68134 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by grind
  clear eq67951
  have eq68432 : (M.op (σ x) (σ x)) = (σ (M.op (k (τ (σ x)) x) (k (τ (σ x)) x))) ∨ x = y := by
    first
    | (have i₁ := eq37151 (σ x)
       have i₂ := eq67738 (σ x)
       grind)
    | exact superpose eq67738 eq37151
    | exact resolve eq37151 eq67738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67738
  have eq68459 : (M.op (σ x) (σ x)) = (σ (M.op (k x x) (k x x))) ∨ x = y := by
    first
    | (have i₁ := eq68432
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq68432
    | exact resolve eq68432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68432
  have eq69035 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq67775 x
       have i₂ := eq68134
       grind)
    | exact superpose eq68134 eq67775
    | exact resolve eq67775 eq68134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67775 eq68134
  have eq69127 : y = (k x x) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq69035
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq69035
    | exact resolve eq69035 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69035
  have eq69128 : y = (k x x) ∨ x = y := by grind
  clear eq69127
  have eq69278 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1379 x x
       have i₂ := eq69128
       grind)
    | exact superpose eq69128 eq1379
    | exact resolve eq1379 eq69128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq69287 : ∀ X0 : G, x = y ∨ (M.op X0 x) = (k X0 x) ∨ (M.op X0 x) = (k X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3728 x x X0
       have i₂ := eq69128
       grind)
    | exact superpose eq69128 eq3728
    | (have j0 := eq3728 x x X0
       grind)
    | exact resolve eq3728 eq69128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728 eq69128
  have eq69306 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq69287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69287
  have eq69307 : (σ y) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq69278
  have eq69819 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq69306 (τ X0)
       grind)
    | exact superpose eq69306 eq16
    | exact resolve eq16 eq69306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq69306
  have eq69972 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq67759 (M.op x x)
       have i₂ := eq69307
       grind)
    | exact superpose eq69307 eq67759
    | exact resolve eq67759 eq69307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67759 eq69307
  have eq69975 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) x)) ∨ x = y := by grind
  clear eq69972
  have eq71320 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq69819 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69819
    | exact resolve eq69819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69819
  have eq71366 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq71320 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq71320
    | exact resolve eq71320 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71320
  have eq75451 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq67680 (σ X1) X0
       grind)
    | exact superpose eq67680 eq13
    | (have j1 := eq67680 (σ X1) X0
       grind)
    | exact resolve eq13 eq67680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67680
  have eq75458 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75451 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq75451
    | (have j0 := eq75451 X0 X1
       grind)
    | exact resolve eq75451 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75451
  have eq76625 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75458 x y
       grind)
    | exact superpose eq75458 eq14
    | (have j1 := eq75458 x y
       grind)
    | exact resolve eq14 eq75458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75458
  have eq76658 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq76625
       have i₂ := eq9585
       grind)
    | exact superpose eq9585 eq76625
    | exact resolve eq76625 eq9585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9585 eq76625
  have eq76671 : y = (k x x) := by
    first
    | (have r₁ := eq76658
       have r₂ := eq68133
       grind)
    | exact resolve eq76658 eq68133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68133 eq76658
  have eq82017 : (M.op (σ y) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq71366 (M.op x x)
       have i₂ := eq69975
       grind)
    | exact superpose eq69975 eq71366
    | exact resolve eq71366 eq69975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69975 eq71366
  have eq82025 : (M.op (σ y) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = y := by grind
  clear eq82017
  have eq83572 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq82025
       have i₂ := eq61493
       grind)
    | exact superpose eq61493 eq82025
    | exact resolve eq82025 eq61493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61493 eq82025
  have eq83590 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = y := by grind
  clear eq83572
  have eq85548 : ∀ X0 : G, (k (τ (σ X0)) X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq33164 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33164
  have eq85549 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq85548 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq85548
    | (have j0 := eq85548 X0
       grind)
    | exact resolve eq85548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85548
  have eq85614 : x ≠ x ∨ x = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85549 x
       have i₂ := eq64511
       grind)
    | exact superpose eq64511 eq85549
    | (have j0 := eq85549 x
       grind)
    | (have r₁ := eq85549 x
       have r₂ := eq64511
       grind)
    | exact resolve eq85549 eq64511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64511 eq85549
  have eq85646 : x = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq85614
  have eq85885 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq37151 (σ x)
       have i₂ := eq85646
       grind)
    | exact superpose eq85646 eq37151
    | exact resolve eq37151 eq85646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37151 eq85646
  have eq86961 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2526
       have i₂ := eq85885
       grind)
    | exact superpose eq85885 eq2526
    | exact resolve eq2526 eq85885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526 eq85885
  have eq87001 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq86961
  have eq87030 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq87001
       grind)
    | exact superpose eq87001 eq9
    | exact resolve eq9 eq87001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87001
  have eq87052 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87030
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq87030
    | exact resolve eq87030 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87030
  have eq87053 : y = (M.op x x) := by grind
  clear eq87052
  have eq87169 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq8 x X0
       have i₂ := eq87053
       grind)
    | exact superpose eq87053 eq8
    | exact resolve eq8 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87053
  have eq90662 : ∀ X0 X1 : G, (k X0 X1) = (k y X1) ∨ (M.op y X0) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62697 X0 X1 y
       have i₂ := eq3486
       grind)
    | exact superpose eq3486 eq62697
    | (have j0 := eq62697 X0 X1 y
       grind)
    | exact resolve eq62697 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62697
  have eq91342 : ∀ X0 : G, (k X0 X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq90662 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90662
  have eq91709 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq91342 X0
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq91342
    | (have j0 := eq91342 X0
       have j1 := eq46 X0 y
       grind)
    | (have r₁ := eq91342 y
       have r₂ := eq46 y y
       grind)
    | exact resolve eq91342 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq91342
  have eq91750 : ∀ X0 X1 : G, (M.op y X0) = (k y X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91709 X0 y
       have j1 := eq3736 X0
       grind)
    | (have r₁ := eq91709 X0 X1
       have r₂ := eq3736 X0
       grind)
    | exact resolve eq91709 eq3736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736 eq91709
  have eq92838 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq91750 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91750
  have eq92839 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq92838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92838
  have eq93075 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq92839 (τ X0)
       grind)
    | exact superpose eq92839 eq17
    | exact resolve eq17 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq96218 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62818 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62818
  have eq96219 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq96218
  have eq103523 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq42 y X0
       have i₂ := eq3936 X0
       grind)
    | exact superpose eq3936 eq42
    | (have j1 := eq3936 X0
       grind)
    | exact resolve eq42 eq3936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq3936
  have eq103528 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq103523 X0
       have i₂ := eq92839 (τ X0)
       grind)
    | exact superpose eq92839 eq103523
    | (have j0 := eq103523 X0
       grind)
    | exact resolve eq103523 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103523
  have eq121963 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq68459
       have i₂ := eq76671
       grind)
    | exact superpose eq76671 eq68459
    | exact resolve eq68459 eq76671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68459 eq76671
  have eq121976 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq121963
       have i₂ := eq3486
       grind)
    | exact superpose eq3486 eq121963
    | exact resolve eq121963 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486 eq121963
  have eq122415 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) X0
       have i₂ := eq121976
       grind)
    | exact superpose eq121976 eq8
    | exact resolve eq8 eq121976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121976
  have eq123373 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq122415 (σ y)
       have i₂ := eq83590
       grind)
    | exact superpose eq83590 eq122415
    | exact resolve eq122415 eq83590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83590 eq122415
  have eq123376 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ x = y := by grind
  clear eq123373
  have eq131191 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ y) X0)
       have i₂ := eq103528 X0
       grind)
    | exact superpose eq103528 eq10
    | (have j1 := eq103528 X0
       grind)
    | exact resolve eq10 eq103528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103528
  have eq131192 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq131191 X0
       have i₂ := eq93075 X0
       grind)
    | exact superpose eq93075 eq131191
    | (have j0 := eq131191 X0
       grind)
    | exact resolve eq131191 eq93075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93075 eq131191
  have eq131193 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq131192 X0
       have j1 := eq96219 (σ y) X0
       grind)
    | (have r₁ := eq131192 x
       have r₂ := eq96219 (σ y) x
       grind)
    | exact resolve eq131192 eq96219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96219 eq131192
  have eq131302 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq131193 (σ X0)
       grind)
    | exact superpose eq131193 eq13
    | exact resolve eq13 eq131193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131193
  have eq131523 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq131302 X0
       have i₂ := eq92839 X0
       grind)
    | exact superpose eq92839 eq131302
    | exact resolve eq131302 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92839 eq131302
  have eq131796 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y x))) ∨ x = y := by
    first
    | (have i₁ := eq123376
       have i₂ := eq131523 (M.op y x)
       grind)
    | exact superpose eq131523 eq123376
    | exact resolve eq123376 eq131523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123376
  have eq132010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq131796
       have i₂ := eq87169 y
       grind)
    | exact superpose eq87169 eq131796
    | exact resolve eq131796 eq87169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87169 eq131796
  have eq132068 : x = y := by
    first
    | (have r₁ := eq132010
       have r₂ := eq14
       grind)
    | exact resolve eq132010 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132010
  have eq132093 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq132068
       grind)
    | exact superpose eq132068 eq14
    | exact resolve eq14 eq132068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132660 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq131523 X0
       have i₂ := eq132068
       grind)
    | exact superpose eq132068 eq131523
    | exact resolve eq131523 eq132068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131523 eq132068
  have eq132896 : False := by grind
  exact eq132896

/-- `Equation3715`: `x ◇ y = (x ◇ x) ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3715 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3715 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3715.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
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
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0)
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq45 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 X1 X2
       have i₂ := eq21 X2 X0
       grind)
    | exact superpose eq21 eq38
    | (have j0 := eq38 X0 X1 X2
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq78 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq81 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq86 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq78
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq39
    | exact resolve eq39 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq39 (τ X1) X0
       grind)
    | exact superpose eq39 eq17
    | (have j1 := eq39 (τ X1) X0
       grind)
    | exact resolve eq17 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq158 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq86
  have eq172 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq158 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq158
    | exact resolve eq158 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq194 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq45 X0 X1 X1
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq45 X2 X1 X2
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq45 X2 X1 X2
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq45 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq45 eq13
    | (have j1 := eq45 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq42 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq42
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq42 x y
       grind)
    | exact superpose eq42 eq14
    | (have j1 := eq42 x y
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X2) X1
       have i₂ := eq42 X2 X0
       grind)
    | exact superpose eq42 eq21
    | (have j1 := eq42 X2 X0
       grind)
    | exact resolve eq21 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq42 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq431 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq431 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1269 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq360
    | (have j0 := eq360 X0
       have j1 := eq91 X0 X1
       grind)
    | exact resolve eq360 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1285 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1342 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq81
    | exact resolve eq81 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1434 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1342 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1342
    | (have j0 := eq1342 X0 X1
       grind)
    | exact resolve eq1342 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1476 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq111
    | exact resolve eq111 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1525 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1476 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1476
    | (have j0 := eq1476 X0 X1
       grind)
    | exact resolve eq1476 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1718 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1
       have i₂ := eq1434 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq1434 (M.op X0 X0) X1
       grind)
    | exact superpose eq1434 eq20
    | (have j1 := eq1434 X0 X1
       grind)
    | exact resolve eq20 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq3104 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq108 X0 X0
       grind)
    | exact superpose eq108 eq22
    | (have j1 := eq108 X0 X0
       grind)
    | exact resolve eq22 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108
  have eq3386 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X0
       have i₂ := eq1718 X0 X1
       grind)
    | exact superpose eq1718 eq447
    | (have j0 := eq447 X0 X1
       have j1 := eq1718 X0 X1
       grind)
    | exact resolve eq447 eq1718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq3431 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq3834 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq447 y x
       grind)
    | exact superpose eq447 eq328
    | (have j1 := eq447 y x
       grind)
    | exact resolve eq328 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq1525 y x
       grind)
    | exact superpose eq1525 eq328
    | (have j1 := eq1525 y x
       grind)
    | (have r₁ := eq328
       have r₂ := eq1525 y x
       grind)
    | exact resolve eq328 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq1525
  have eq3839 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq3836
  have eq3841 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq3834
  have eq5707 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq172 x
       have i₂ := eq3839
       grind)
    | exact superpose eq3839 eq172
    | exact resolve eq172 eq3839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq3839
  have eq5757 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq5707
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5707
    | exact resolve eq5707 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5707
  have eq5758 : x = (k x y) := by grind
  clear eq5757
  have eq6055 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq194 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq6056 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6055 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6055
  have eq6113 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq36 y X0 x
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq36
    | (have j0 := eq36 y X0 x
       grind)
    | exact resolve eq36 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq6114 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq45 y x X0
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq45
    | (have j0 := eq45 y x X0
       grind)
    | exact resolve eq45 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq6118 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq447 y x
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq447
    | (have j0 := eq447 y x
       grind)
    | exact resolve eq447 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq6619 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq223 x y X0
       grind)
    | exact superpose eq223 eq14
    | (have j1 := eq223 x y X0
       grind)
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq6788 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq6619 X0
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq6619
    | (have j0 := eq6619 X0
       grind)
    | exact resolve eq6619 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6619
  have eq6849 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq312
    | (have j0 := eq312 X1 (τ X0)
       grind)
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq7018 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6849 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq6849
    | (have j0 := eq6849 X0 X1
       grind)
    | exact resolve eq6849 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq6849
  have eq7031 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7018 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7018
    | (have j0 := eq7018 X0 X1
       grind)
    | exact resolve eq7018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7128 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5758
       have i₂ := eq6056 x y
       grind)
    | exact superpose eq6056 eq5758
    | (have j1 := eq6056 x y
       grind)
    | exact resolve eq5758 eq6056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6056
  have eq7301 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115 y x
       have i₂ := eq7128
       grind)
    | exact superpose eq7128 eq115
    | (have j0 := eq115 y x
       grind)
    | (have r₁ := eq115 y x
       have r₂ := eq7128
       grind)
    | (have r₁ := eq115 x y
       have r₂ := eq7128
       grind)
    | exact resolve eq115 eq7128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7128
  have eq7314 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq7301
  have eq7810 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq354 y X0 x
       grind)
    | exact superpose eq354 eq14
    | (have j1 := eq354 y X0 x
       grind)
    | exact resolve eq14 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq7847 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7810 X0
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq7810
    | (have j0 := eq7810 X0
       grind)
    | exact resolve eq7810 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7810
  have eq9063 : x ≠ (M.op x x) ∨ x = (M.op x y) := by grind
  have eq9764 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6118
       have i₂ := eq6114 y
       grind)
    | exact superpose eq6114 eq6118
    | exact resolve eq6118 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6118
  have eq9811 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6113 y
       have i₂ := eq6114 y
       grind)
    | exact superpose eq6114 eq6113
    | exact resolve eq6113 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113 eq6114
  have eq9812 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq9811
  have eq9814 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq9764
  have eq10001 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq9814
  have eq13434 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq3841
       grind)
    | exact superpose eq3841 eq20
    | exact resolve eq20 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3841
  have eq13488 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13434
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq13434
    | exact resolve eq13434 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13434
  have eq14168 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq13488
       grind)
    | exact superpose eq13488 eq9
    | exact resolve eq9 eq13488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13488
  have eq14240 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14168
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq14168
    | exact resolve eq14168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14168
  have eq14243 : y = (k y y) := by
    first
    | (have j1 := eq115 y y
       grind)
    | (have r₁ := eq14240
       have r₂ := eq115 y y
       grind)
    | exact resolve eq14240 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14240
  have eq14975 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq360 y
       have i₂ := eq14243
       grind)
    | exact superpose eq14243 eq360
    | (have j0 := eq360 y
       grind)
    | exact resolve eq360 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq14243
  have eq15001 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq14975
  have eq30197 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3431 x y
       have i₂ := eq7314
       grind)
    | exact superpose eq7314 eq3431
    | (have j0 := eq3431 x x
       grind)
    | exact resolve eq3431 eq7314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431 eq7314
  have eq30529 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30197
       have r₂ := eq9063
       grind)
    | exact resolve eq30197 eq9063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9063 eq30197
  have eq30874 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30529
       have i₂ := eq9812
       grind)
    | exact superpose eq9812 eq30529
    | exact resolve eq30529 eq9812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9812 eq30529
  have eq30972 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq30874
  have eq34982 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq5758
       have i₂ := eq7031 x y
       grind)
    | exact superpose eq7031 eq5758
    | (have j1 := eq7031 x y
       grind)
    | exact resolve eq5758 eq7031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758 eq7031
  have eq35184 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34982
       have r₂ := eq10001
       grind)
    | exact resolve eq34982 eq10001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10001 eq34982
  have eq43337 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6788 X0
       have i₂ := eq30972
       grind)
    | exact superpose eq30972 eq6788
    | (have j0 := eq6788 X0
       grind)
    | exact resolve eq6788 eq30972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52922 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3104 x x
       have i₂ := eq35184
       grind)
    | exact superpose eq35184 eq3104
    | exact resolve eq3104 eq35184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104 eq35184
  have eq52946 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq52922 X0
       have j1 := eq43337 X0
       grind)
    | (have r₁ := eq52922 X0
       have r₂ := eq43337 X0
       grind)
    | exact resolve eq52922 eq43337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43337 eq52922
  have eq58335 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15001
       have i₂ := eq52946 (σ y)
       grind)
    | exact superpose eq52946 eq15001
    | exact resolve eq15001 eq52946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52946
  have eq58451 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58335
       grind)
    | exact superpose eq58335 eq14
    | exact resolve eq14 eq58335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58335
  have eq58512 : x = (M.op x y) := by
    first
    | (have r₁ := eq58451
       have r₂ := eq30972
       grind)
    | exact resolve eq58451 eq30972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30972 eq58451
  have eq58536 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq6788 X0
       have i₂ := eq58512
       grind)
    | exact superpose eq58512 eq6788
    | (have j0 := eq6788 X0
       grind)
    | exact resolve eq6788 eq58512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6788
  have eq58537 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7847 X0
       have i₂ := eq58512
       grind)
    | exact superpose eq58512 eq7847
    | (have j0 := eq7847 X0
       grind)
    | exact resolve eq7847 eq58512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847
  have eq58585 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq58537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58537
  have eq58586 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq58536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58536
  have eq58864 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58585 (σ x)
       grind)
    | exact superpose eq58585 eq14
    | exact resolve eq14 eq58585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58868 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq15001
       have i₂ := eq58585 (σ y)
       grind)
    | exact superpose eq58585 eq15001
    | exact resolve eq15001 eq58585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15001 eq58585
  have eq58922 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58868
       have i₂ := eq58586 (σ x)
       grind)
    | exact superpose eq58586 eq58868
    | exact resolve eq58868 eq58586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58586 eq58868
  have eq58923 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58864
       have i₂ := eq58512
       grind)
    | exact superpose eq58512 eq58864
    | exact resolve eq58864 eq58512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58864
  have eq59090 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq58923
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq58923
    | exact resolve eq58923 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58923
  have eq59323 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1285 x X0
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq1285
    | (have j0 := eq1285 x X0
       grind)
    | exact resolve eq1285 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq59334 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102 (σ x) x
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq102
    | exact resolve eq102 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq58922
  have eq59491 : (τ (σ y)) = (k (τ (σ x)) x) := by
    first
    | (have r₁ := eq59334
       have r₂ := eq59090
       grind)
    | exact resolve eq59334 eq59090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59334
  have eq59499 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq59323 X0
       grind)
    | (have r₁ := eq59323 X0
       have r₂ := eq59090
       grind)
    | exact resolve eq59323 eq59090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59323
  have eq59522 : (k x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq59491
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq59491
    | exact resolve eq59491 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59491
  have eq59538 : y = (k x x) := by
    first
    | (have i₁ := eq59522
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq59522
    | exact resolve eq59522 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59522
  have eq59546 : y = (M.op x x) := by
    first
    | (have i₁ := eq59538
       have i₂ := eq59499 x
       grind)
    | exact superpose eq59499 eq59538
    | exact resolve eq59538 eq59499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59499 eq59538
  have eq59601 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq21 x X0
       have i₂ := eq59546
       grind)
    | exact superpose eq59546 eq21
    | exact resolve eq21 eq59546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq60160 : x = (M.op x x) := by
    first
    | (have i₁ := eq58512
       have i₂ := eq59601 x
       grind)
    | exact superpose eq59601 eq58512
    | exact resolve eq58512 eq59601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58512 eq59601
  have eq60446 : x = y := by
    first
    | (have i₁ := eq59546
       have i₂ := eq60160
       grind)
    | exact superpose eq60160 eq59546
    | exact resolve eq59546 eq60160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59546 eq60160
  have eq60715 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq59090
       have i₂ := eq60446
       grind)
    | exact superpose eq60446 eq59090
    | exact resolve eq59090 eq60446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59090 eq60446
  have eq60716 : False := by grind
  exact eq60716
